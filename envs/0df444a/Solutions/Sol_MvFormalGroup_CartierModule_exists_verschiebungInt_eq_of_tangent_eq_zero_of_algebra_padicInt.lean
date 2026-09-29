-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fd918fb7-fdef-5a57-bbc3-d19bc86e88b4

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_pow_eq
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_frobFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_frobFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_addFam_projFam_and_subst_artinHasse_projFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam
import Theorems.Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_projFam
import Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero
import Theorems.Thm_MvFormalGroup_ArtinHasse_subst_addFam_map_coord
import Theorems.Thm_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open MvPowerSeries

noncomputable section

namespace B23K4

section WV
variable {σ : Type*} {R : Type u} [CommRing R] (w : σ → ℕ)

def WV (N : ℕ) (g : MvPowerSeries σ R) : Prop :=
  ∀ e : σ →₀ ℕ, Finsupp.weight w e < N → coeff e g = 0

variable {w}

theorem WV.mono {N N' : ℕ} {g : MvPowerSeries σ R} (h : WV w N' g) (hle : N ≤ N') : WV w N g :=
  fun e he => h e (lt_of_lt_of_le he hle)

theorem WV.zero_wt (g : MvPowerSeries σ R) : WV w 0 g := fun e he => absurd he (Nat.not_lt_zero _)

theorem WV.zero (N : ℕ) : WV w N (0 : MvPowerSeries σ R) := fun e _ => by rw [map_zero]

theorem WV.add {N : ℕ} {g h : MvPowerSeries σ R} (hg : WV w N g) (hh : WV w N h) : WV w N (g + h) :=
  fun e he => by rw [map_add, hg e he, hh e he, add_zero]

theorem WV.neg {N : ℕ} {g : MvPowerSeries σ R} (hg : WV w N g) : WV w N (-g) :=
  fun e he => by rw [map_neg, hg e he, neg_zero]

theorem WV.sub {N : ℕ} {g h : MvPowerSeries σ R} (hg : WV w N g) (hh : WV w N h) : WV w N (g - h) :=
  fun e he => by rw [map_sub, hg e he, hh e he, sub_zero]

theorem WV.sum {N : ℕ} {ι : Type*} (s : Finset ι) {g : ι → MvPowerSeries σ R}
    (h : ∀ i ∈ s, WV w N (g i)) : WV w N (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WV.zero (w := w) N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem WV.mul {M M' : ℕ} {g h : MvPowerSeries σ R} (hg : WV w M g) (hh : WV w M' h) :
    WV w (M + M') (g * h) := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hwt : Finsupp.weight w x.1 + Finsupp.weight w x.2 = Finsupp.weight w e := by
    rw [← map_add, hx']
  by_cases h1 : Finsupp.weight w x.1 < M
  · rw [hg _ h1, zero_mul]
  · have h2 : Finsupp.weight w x.2 < M' := by omega
    rw [hh _ h2, mul_zero]

theorem WV.mul_right {N : ℕ} {g : MvPowerSeries σ R} (hg : WV w N g) (h : MvPowerSeries σ R) :
    WV w N (g * h) := by
  simpa using hg.mul (WV.zero_wt (w := w) h)

theorem WV.mul_left {N : ℕ} {g : MvPowerSeries σ R} (hg : WV w N g) (h : MvPowerSeries σ R) :
    WV w N (h * g) := by
  rw [mul_comm]; exact hg.mul_right h

theorem WV.smul {N : ℕ} {g : MvPowerSeries σ R} (hg : WV w N g) (r : R) : WV w N (r • g) :=
  fun e he => by rw [map_smul, hg e he, smul_zero]

theorem WV.pow {M : ℕ} {g : MvPowerSeries σ R} (hg : WV w M g) (m : ℕ) : WV w (m * M) (g ^ m) := by
  induction m with
  | zero => (have h__af := WV.zero_wt (w := w) (g ^ 0); simp at h__af ⊢; exact h__af)
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hg

theorem WV.of_dvd {N : ℕ} {g h : MvPowerSeries σ R} (hg : WV w N g) (hdvd : g ∣ h) : WV w N h := by
  obtain ⟨q, rfl⟩ := hdvd
  exact hg.mul_right q

theorem WV.finsuppProd {σ' : Type*} {c : σ' → MvPowerSeries σ R} {v : σ' → ℕ}
    (hc : ∀ j, WV w (v j) (c j)) (D : σ' →₀ ℕ) :
    WV w (Finsupp.weight v D) (D.prod fun j l => c j ^ l) := by
  classical
  induction D using Finsupp.induction with
  | zero => simpa using WV.zero_wt (w := w) (1 : MvPowerSeries σ R)
  | single_add j l D hjD hl ih =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _), map_add,
      Finsupp.weight_single, smul_eq_mul]
    exact ((hc j).pow l).mul ih

theorem WV.finsuppProd_of_mem {σ' : Type*} {c : σ' → MvPowerSeries σ R} {N : ℕ} {j₀ : σ'}
    (hc : WV w N (c j₀)) (D : σ' →₀ ℕ) (hj : j₀ ∈ D.support) :
    WV w N (D.prod fun j l => c j ^ l) := by
  classical
  rw [← Finsupp.mul_prod_erase D j₀ (fun j l => c j ^ l) hj]
  have h1 : 1 ≤ D j₀ := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have := (hc.pow (D j₀)).mul_right ((Finsupp.erase j₀ D).prod fun j l => c j ^ l)
  exact this.mono (by nlinarith)

theorem WV.finsuppProd_sub {σ' : Type*} {c c' : σ' → MvPowerSeries σ R} {N : ℕ}
    (hc : ∀ j, WV w N (c j - c' j)) (D : σ' →₀ ℕ) :
    WV w N ((D.prod fun j l => c j ^ l) - D.prod fun j l => c' j ^ l) := by
  classical
  induction D using Finsupp.induction with
  | zero => simpa using WV.zero (w := w) N
  | single_add j l D hjD hl ih =>
    rw [Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun j' l' => c j' ^ l') (pow_zero _),
      Finsupp.prod_single_index (h := fun j' l' => c' j' ^ l') (pow_zero _)]
    have hp : WV w N (c j ^ l - c' j ^ l) := (hc j).of_dvd (sub_dvd_pow_sub_pow _ _ l)
    have e1 : c j ^ l * (D.prod fun j l => c j ^ l) - c' j ^ l * (D.prod fun j l => c' j ^ l) =
        (c j ^ l - c' j ^ l) * (D.prod fun j l => c j ^ l) +
          c' j ^ l * ((D.prod fun j l => c j ^ l) - D.prod fun j l => c' j ^ l) := by ring
    rw [e1]
    exact (hp.mul_right _).add (ih.mul_left _)

theorem WV.subst_sub {σ' : Type*} {c c' : σ' → MvPowerSeries σ R} (hsc : HasSubst c)
    (hsc' : HasSubst c') {N : ℕ} (hc : ∀ j, WV w N (c j - c' j)) (g : MvPowerSeries σ' R) :
    WV w N (subst c g - subst c' g) := by
  intro e he
  rw [map_sub, coeff_subst hsc, coeff_subst hsc',
    ← finsum_sub_distrib (coeff_subst_finite hsc g e) (coeff_subst_finite hsc' g e)]
  refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
  rw [← smul_sub, ← map_sub, WV.finsuppProd_sub hc D e he, smul_zero]

theorem WV.subst_of_raise {τ : Type*} {w' : τ → ℕ} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (hw : ∀ n, WV w' (w n) (a n)) {N : ℕ} {g : MvPowerSeries σ R} (hg : WV w N g) :
    WV w' N (subst a g) := by
  intro e he
  rw [coeff_subst ha]
  refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
  by_cases hD : Finsupp.weight w D < N
  · rw [hg D hD, zero_smul]
  · rw [WV.finsuppProd hw D e (by omega), smul_zero]

end WV

section K4
open MvFormalGroup MvFormalGroup.CartierModule MvFormalGroup.WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
  {Φ : MvFormalGroup d R} [Φ.IsComm]

abbrev wN (p : ℕ) : ℕ → ℕ := fun m => p ^ m

def Cong (N : ℕ) (a b : CartierModule p Φ) : Prop :=
  ∀ j, WV (wN p) N (a.toPowerSeries j - b.toPowerSeries j)

theorem Cong.refl (N : ℕ) (a : CartierModule p Φ) : Cong N a a :=
  fun j => by rw [sub_self]; exact WV.zero N

theorem Cong.symm {N : ℕ} {a b : CartierModule p Φ} (h : Cong N a b) : Cong N b a :=
  fun j => by rw [← neg_sub]; exact (h j).neg

theorem Cong.trans {N : ℕ} {a b c : CartierModule p Φ} (h : Cong N a b) (h' : Cong N b c) :
    Cong N a c :=
  fun j => by rw [← sub_add_sub_cancel]; exact (h j).add (h' j)

theorem Cong.mono {N N' : ℕ} {a b : CartierModule p Φ} (h : Cong N' a b) (hle : N ≤ N') :
    Cong N a b :=
  fun j => (h j).mono hle

theorem hasSubst_elim (a b : CartierModule p Φ) :
    HasSubst (Sum.elim a.toPowerSeries b.toPowerSeries) := by
  apply hasSubst_of_constantCoeff_zero
  rintro (j | j)
  · exact a.constantCoeff_eq_zero j
  · exact b.constantCoeff_eq_zero j

theorem Cong.add {N : ℕ} {a a' b b' : CartierModule p Φ} (ha : Cong N a a') (hb : Cong N b b') :
    Cong N (a + b) (a' + b') := by
  intro j
  rw [toPowerSeries_add, toPowerSeries_add]
  refine WV.subst_sub (hasSubst_elim a b) (hasSubst_elim a' b') ?_ (Φ.toPowerSeries j)
  rintro (l | l)
  · exact ha l
  · exact hb l

theorem Cong.sub_left {N : ℕ} {a a' : CartierModule p Φ} (ha : Cong N a a') (b : CartierModule p Φ) :
    Cong N (a - b) (a' - b) := by
  intro j
  rw [toPowerSeries_sub, toPowerSeries_sub]
  have hE : ∀ x : CartierModule p Φ,
      HasSubst (Sum.elim x.toPowerSeries (negSeries Φ b.toPowerSeries)) := fun x => by
    apply hasSubst_of_constantCoeff_zero
    rintro (l | l)
    · exact x.constantCoeff_eq_zero l
    · exact constantCoeff_negSeries Φ b.toPowerSeries l
  refine WV.subst_sub (hE a) (hE a') ?_ (Φ.toPowerSeries j)
  rintro (l | l)
  · exact ha l
  · show WV (wN p) N (negSeries Φ b.toPowerSeries l - negSeries Φ b.toPowerSeries l)
    rw [sub_self]; exact WV.zero N

theorem Cong.add_small {N : ℕ} (a : CartierModule p Φ) {b : CartierModule p Φ}
    (hb : ∀ l, WV (wN p) N (b.toPowerSeries l)) : Cong N (a + b) a := by
  intro j
  rw [toPowerSeries_add]
  have h0 : subst (Sum.elim a.toPowerSeries fun _ => (0 : MvPowerSeries ℕ R)) (Φ.toPowerSeries j) =
      a.toPowerSeries j := subst_elim_zero_right Φ a.constantCoeff_eq_zero j
  rw [show subst (Sum.elim a.toPowerSeries b.toPowerSeries) (Φ.toPowerSeries j) - a.toPowerSeries j =
      subst (Sum.elim a.toPowerSeries b.toPowerSeries) (Φ.toPowerSeries j) -
        subst (Sum.elim a.toPowerSeries fun _ => (0 : MvPowerSeries ℕ R)) (Φ.toPowerSeries j) by
    rw [h0]]
  have hE' : HasSubst (Sum.elim a.toPowerSeries fun _ : Fin d => (0 : MvPowerSeries ℕ R)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (l | l)
    · exact a.constantCoeff_eq_zero l
    · exact map_zero _
  refine WV.subst_sub (hasSubst_elim a b) hE' ?_ (Φ.toPowerSeries j)
  rintro (l | l)
  · show WV (wN p) N (a.toPowerSeries l - a.toPowerSeries l)
    rw [sub_self]; exact WV.zero N
  · show WV (wN p) N (b.toPowerSeries l - 0)
    rw [sub_zero]; exact hb l

theorem WV_addFam (n : ℕ) : WV (weight p fun _ : Fin 2 => 1) (p ^ n) (addFam p R n) := by
  intro e he
  by_contra h
  have := weight_eq_of_coeff_addFam_ne_zero (p := p) (R := R) h
  omega

theorem WV_blk (i : Fin 2) (m : ℕ) :
    WV (weight p fun _ : Fin 2 => 1) (p ^ m) (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R) := by
  classical
  intro e he
  rw [coeff_X]
  split_ifs with h
  · subst h
    rw [Finsupp.weight_single, weight_apply, one_mul, smul_eq_mul, one_mul] at he
    exact absurd he (lt_irrefl _)
  · rfl

end K4
end B23K4

namespace B23K5

open MvFormalGroup MvFormalGroup.CartierModule MvFormalGroup.WittLaw B23K4

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}

def IsLamHom (Φ : MvFormalGroup d R) (G : Fin d → MvPowerSeries ℕ R) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
  (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))

abbrev omg (R : Type u) [CommRing R] : ℕ → PowerSeries R :=
  fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)

theorem precomp_hom {Φ : MvFormalGroup d R} {S₁ S₂ : ℕ → MvPowerSeries (Fin 2 × ℕ) R}
    (hS₁ : HasSubst S₁) (hS₂ : HasSubst S₂)
    {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u) (hu0 : ∀ m, MvPowerSeries.constantCoeff (u m) = 0)
    (huS : ∀ m, subst S₁ (u m) = subst (pairFam u) (S₂ m))
    {G : Fin d → MvPowerSeries ℕ R} (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hG : ∀ j, subst S₂ (G j) = subst (Sum.elim (inBlk 0 G) (inBlk 1 G)) (Φ.toPowerSeries j)) :
    (∀ j, MvPowerSeries.constantCoeff (subst u (G j)) = 0) ∧
    ∀ j, subst S₁ (subst u (G j)) =
      subst (Sum.elim (inBlk 0 (fun l => subst u (G l))) (inBlk 1 (fun l => subst u (G l))))
        (Φ.toPowerSeries j) := by
  refine ⟨fun j => constantCoeff_subst_eq_zero hu hu0 (hG0 j), fun j => ?_⟩
  have hP := hasSubst_pairFam hu hu0
  rw [subst_comp_subst_apply hu hS₁]
  have hfam : (fun n => subst S₁ (u n)) = fun n => subst (pairFam u) (S₂ n) := funext huS
  rw [hfam, ← subst_comp_subst_apply hS₂ hP, hG j,
    subst_subst_elim Φ (constantCoeff_inBlk 0 hG0) (constantCoeff_inBlk 1 hG0) hP]
  congr 1
  funext s
  rcases s with l | l
  · exact subst_pairFam_subst_blk hu hu0 0 (G l)
  · exact subst_pairFam_subst_blk hu hu0 1 (G l)

section AH
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

def ahFam : ℕ → MvPowerSeries ℕ R := fun m =>
  (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p m)) : MvPowerSeries ℕ R)

theorem ahFam_apply (m : ℕ) : ahFam p R m =
    (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p m)) : MvPowerSeries ℕ R) := rfl

variable {p R}

theorem weight_eq_of_coeff_ahFam_ne_zero {m : ℕ} {e : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff e (ahFam p R m) ≠ 0) :
    Finsupp.weight (fun k : ℕ => p ^ k) e = m + 1 := by
  rw [ahFam_apply, MvPolynomial.coeff_coe, MvPolynomial.coeff_map] at h
  have h' : MvPolynomial.coeff e (ArtinHasse.coord p m) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact ArtinHasse.isWeightedHomogeneous_coord p m h'

theorem WV_ahFam (m : ℕ) : WV (fun k : ℕ => p ^ k) (m + 1) (ahFam p R m) := by
  intro e he
  by_contra h
  have := weight_eq_of_coeff_ahFam_ne_zero h
  omega

theorem constantCoeff_ahFam (m : ℕ) : MvPowerSeries.constantCoeff (ahFam p R m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact WV_ahFam m 0 (by simp)

theorem hasSubst_ahFam : HasSubst (ahFam p R) := by
  refine ⟨fun m => by rw [constantCoeff_ahFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (Finsupp.weight (fun k : ℕ => p ^ k) e)).subset fun m hm => ?_
  have hw := weight_eq_of_coeff_ahFam_ne_zero hm
  show m ≤ Finsupp.weight (fun k : ℕ => p ^ k) e
  omega

end AH

theorem subst_zero_family {σ τ : Type*} (g : MvPowerSeries σ R) (hg : MvPowerSeries.constantCoeff g = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = 0 := by
  classical
  ext e
  rw [coeff_subst HasSubst.zero, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
  by_cases hD : D = 0
  · subst hD
    rw [coeff_zero_eq_constantCoeff_apply, hg, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hD
    rw [← Finsupp.mul_prod_erase D s _ (Finsupp.mem_support_iff.mpr hs), zero_pow hs, zero_mul,
      map_zero, smul_zero]

theorem negSeries_eq_subst_invSeries (Φ : MvFormalGroup d R) {τ : Type*}
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0) :
    negSeries Φ a = fun i => subst a (invSeries Φ i) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hy : ∀ j, (subst a (invSeries Φ j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero hsa ha (constantCoeff_invSeries Φ j)
  refine (negSeries_unique Φ ha hy fun i => ?_).symm
  have h := congrArg (subst a) (subst_elim_X_invSeries Φ i)
  rw [← coe_substAlgHom hsa, map_zero, coe_substAlgHom,
    subst_subst_elim Φ (fun j => constantCoeff_X j) (constantCoeff_invSeries Φ) hsa] at h
  convert h using 2
  funext s
  rcases s with l | l
  · exact (subst_X hsa l).symm
  · rfl

theorem subst_negSeries' (Φ : MvFormalGroup d R) {τ τ' : Type*}
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0)
    {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ s, (b s).constantCoeff = 0) :
    (fun i => subst b (negSeries Φ a i)) = negSeries Φ fun i => subst b (a i) := by
  have hab : ∀ j, (subst b (a j)).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero hb hb0 (ha j)
  rw [negSeries_eq_subst_invSeries Φ ha, negSeries_eq_subst_invSeries Φ hab]
  funext i
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hb]

section Decomp
variable (Φ : MvFormalGroup d R) [Φ.IsComm]

theorem hasSubst_omg : HasSubst (omg R) := by
  classical
  refine ⟨fun m => ?_, fun e => ?_⟩
  · show IsNilpotent (MvPowerSeries.constantCoeff ((PowerSeries.X : PowerSeries R) ^ (m + 1)))
    rw [map_pow, show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 from
      PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero m)]
    exact IsNilpotent.zero
  · refine (Set.finite_le_nat (e ())).subset fun m hm => ?_
    show m ≤ e ()
    by_contra hlt
    apply hm
    show MvPowerSeries.coeff e ((PowerSeries.X : PowerSeries R) ^ (m + 1)) = 0
    rw [show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, coeff_X_pow, if_neg]
    intro h
    have := congrArg (fun f : Unit →₀ ℕ => f ()) h
    simp only [Finsupp.single_eq_same] at this
    omega

def homOfCurve (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    Fin d → MvPowerSeries ℕ R :=
  Classical.choose (MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq Φ γ hγ)

theorem homOfCurve_isLamHom (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    IsLamHom Φ (homOfCurve Φ γ hγ) :=
  ⟨(Classical.choose_spec (MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq Φ γ hγ)).1,
   (Classical.choose_spec (MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq Φ γ hγ)).2.1⟩

theorem omg_homOfCurve (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0)
    (j : Fin d) : subst (omg R) (homOfCurve Φ γ hγ j) = γ j :=
  (Classical.choose_spec (MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq Φ γ hγ)).2.2 j

def monoCurve (c : Fin d → R) (r : ℕ) : Fin d → PowerSeries R := fun j => PowerSeries.monomial r (c j)

omit hp in
theorem constantCoeff_monoCurve (c : Fin d → R) {r : ℕ} (hr : r ≠ 0) (j : Fin d) :
    PowerSeries.constantCoeff (monoCurve c r j) = 0 := by
  rw [monoCurve, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial,
    if_neg (Ne.symm hr)]

def qOf (p n : ℕ) : ℕ := by classical exact if ∃ k : ℕ, n = p ^ k then p else n
def rOf (p n : ℕ) : ℕ := by classical exact if h : ∃ k : ℕ, n = p ^ k then p ^ (Classical.choose h - 1) else 1

theorem rOf_mul_qOf {n : ℕ} (hn : 2 ≤ n) : rOf p n * qOf p n = n := by
  classical
  unfold rOf qOf
  split_ifs with h
  · have hk := Classical.choose_spec h
    have hk0 : Classical.choose h ≠ 0 := by
      intro h0; rw [h0, pow_zero] at hk; omega
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    exact hk.symm
  · exact one_mul n

theorem qOf_pos {n : ℕ} (hn : 2 ≤ n) : 0 < qOf p n := by
  classical
  unfold qOf; split_ifs
  · exact hp.out.pos
  · omega

theorem rOf_ne_zero (n : ℕ) : rOf p n ≠ 0 := by
  classical
  unfold rOf; split_ifs
  · exact pow_ne_zero _ hp.out.ne_zero
  · exact one_ne_zero

theorem rOf_ppow (k : ℕ) : rOf p (p ^ (k + 1)) = p ^ k := by
  classical
  unfold rOf
  have h : ∃ k' : ℕ, p ^ (k + 1) = p ^ k' := ⟨k + 1, rfl⟩
  rw [dif_pos h]
  have hk := Classical.choose_spec h
  have := Nat.pow_right_injective hp.out.two_le hk
  rw [← this, Nat.add_sub_cancel]

theorem qOf_ppow (k : ℕ) : qOf p (p ^ (k + 1)) = p := by
  classical
  unfold qOf
  rw [if_pos ⟨k + 1, rfl⟩]

def EOf (c : Fin d → R) (n : ℕ) : Fin d → MvPowerSeries ℕ R :=
  homOfCurve Φ (monoCurve c (rOf p n)) (constantCoeff_monoCurve c (rOf_ne_zero (p := p) n))

theorem EOf_isLamHom (c : Fin d → R) (n : ℕ) : IsLamHom Φ (EOf (p := p) Φ c n) :=
  homOfCurve_isLamHom Φ _ _

theorem omg_EOf (c : Fin d → R) (n : ℕ) (j : Fin d) :
    subst (omg R) (EOf (p := p) Φ c n j) = PowerSeries.monomial (rOf p n) (c j) :=
  omg_homOfCurve Φ _ _ j

def HOf (c : Fin d → R) (n : ℕ) : Fin d → MvPowerSeries ℕ R := fun j =>
  subst (MvFormalGroup.BigWittLaw.frobFam R (qOf p n)) (EOf (p := p) Φ c n j)

theorem HOf_isLamHom (c : Fin d → R) {n : ℕ} (hn : 2 ≤ n) : IsLamHom Φ (HOf (p := p) Φ c n) := by
  have hq : 0 < qOf p n := qOf_pos (p := p) hn
  have hE := EOf_isLamHom (p := p) Φ c n
  exact precomp_hom (Φ := Φ) (BigWittLaw.hasSubst_addFam R) (BigWittLaw.hasSubst_addFam R)
    (BigWittLaw.hasSubst_frobFam R (qOf p n)) (BigWittLaw.constantCoeff_frobFam R hq.ne')
    (fun m => MvFormalGroup.BigWittLaw.subst_addFam_frobFam R (qOf p n) hq m) hE.1 hE.2

theorem omg_HOf (c : Fin d → R) {n : ℕ} (hn : 2 ≤ n) (j : Fin d) :
    subst (omg R) (HOf (p := p) Φ c n j) = PowerSeries.monomial n (c j) := by
  have hq : 0 < qOf p n := qOf_pos (p := p) hn
  have hE := EOf_isLamHom (p := p) Φ c n
  rw [HOf, MvFormalGroup.BigWittLaw.subst_pow_subst_frobFam R (qOf p n) hq _ (hE.1 j), omg_EOf]
  show MvPowerSeries.expand (qOf p n) hq.ne' (MvPowerSeries.monomial (Finsupp.single () (rOf p n)) (c j)) =
    MvPowerSeries.monomial (Finsupp.single () n) (c j)
  rw [expand_monomial, Finsupp.smul_single, smul_eq_mul, mul_comm, rOf_mul_qOf (p := p) hn]

def cOf (D : Fin d → MvPowerSeries ℕ R) (n : ℕ) : Fin d → R := fun j => PowerSeries.coeff n (subst (omg R) (D j))

def stepD (D : Fin d → MvPowerSeries ℕ R) (n : ℕ) : Fin d → MvPowerSeries ℕ R := fun j =>
  subst (Sum.elim D (negSeries Φ (HOf (p := p) Φ (cOf D n) n))) (Φ.toPowerSeries j)

theorem stepD_spec (D : Fin d → MvPowerSeries ℕ R) {n : ℕ} (hn : 2 ≤ n) (hD : IsLamHom Φ D)
    (hDn : ∀ (j : Fin d) (k : ℕ), k < n → PowerSeries.coeff k (subst (omg R) (D j)) = 0) :
    IsLamHom Φ (stepD (p := p) Φ D n) ∧
      ∀ (j : Fin d) (k : ℕ), k < n + 1 → PowerSeries.coeff k (subst (omg R) (stepD (p := p) Φ D n j)) = 0 := by
  have hH := HOf_isLamHom (p := p) Φ (cOf D n) hn
  have key := MvFormalGroup.BigWittLaw.subst_elim_negSeries_hom_and_coeff_eq_zero Φ D
    (HOf (p := p) Φ (cOf D n) n) hD.1 hD.2 hH.1 hH.2 n (by omega) hDn
    (fun j k hk => by
      rw [omg_HOf (p := p) Φ _ hn, PowerSeries.coeff_monomial, if_neg (by omega)])
    (fun j => by rw [omg_HOf (p := p) Φ _ hn, PowerSeries.coeff_monomial, if_pos rfl]; rfl)
  exact ⟨⟨key.1, key.2.1⟩, key.2.2⟩

end Decomp

section Seq
variable [Algebra ℤ_[p] R] (Φ : MvFormalGroup d R) [Φ.IsComm] (f : CartierModule p Φ)

def Dseq : ℕ → (Fin d → MvPowerSeries ℕ R)
  | 0 => fun j => subst (MvFormalGroup.BigWittLaw.projFam R p) (f.toPowerSeries j)
  | i + 1 => stepD (p := p) Φ (Dseq i) (i + 2)

theorem Dseq_zero : Dseq (p := p) Φ f 0 = fun j => subst (MvFormalGroup.BigWittLaw.projFam R p) (f.toPowerSeries j) := rfl
theorem Dseq_succ (i : ℕ) : Dseq (p := p) Φ f (i + 1) = stepD (p := p) Φ (Dseq (p := p) Φ f i) (i + 2) := rfl

theorem isLamHom_comp_proj : IsLamHom Φ (fun j => subst (MvFormalGroup.BigWittLaw.projFam R p) (f.toPowerSeries j)) := by
  have h2 : 2 ≤ p := hp.out.two_le
  exact precomp_hom (Φ := Φ) (BigWittLaw.hasSubst_addFam R) (WittLaw.hasSubst_addFam p R)
    (BigWittLaw.hasSubst_projFam R h2) (BigWittLaw.constantCoeff_projFam R p)
    (fun m => (MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam p R).1 m)
    f.constantCoeff_eq_zero f.subst_addFam

theorem omg_comp_proj (j : Fin d) :
    subst (omg R) (subst (MvFormalGroup.BigWittLaw.projFam R p) (f.toPowerSeries j)) = curve f j := by
  rw [MvFormalGroup.BigWittLaw.subst_pow_subst_projFam p R _ (f.constantCoeff_eq_zero j)]
  rfl

theorem Dseq_spec (hf : tangent f = 0) :
    ∀ i, IsLamHom Φ (Dseq (p := p) Φ f i) ∧
      ∀ (j : Fin d) (k : ℕ), k < i + 2 → PowerSeries.coeff k (subst (omg R) (Dseq (p := p) Φ f i j)) = 0 := by
  intro i
  induction i with
  | zero =>
    refine ⟨isLamHom_comp_proj (p := p) Φ f, fun j k hk => ?_⟩
    rw [Dseq_zero, omg_comp_proj]
    interval_cases k
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact constantCoeff_curve f j
    · rw [coeff_one_curve, hf]; rfl
  | succ i ih =>
    rw [Dseq_succ]
    exact stepD_spec (p := p) Φ _ (by omega) ih.1 ih.2

def toCM (G : Fin d → MvPowerSeries ℕ R) (hG : IsLamHom Φ G) : CartierModule p Φ where
  toPowerSeries := fun j => subst (ahFam p R) (G j)
  constantCoeff_eq_zero := (precomp_hom (Φ := Φ) (WittLaw.hasSubst_addFam p R) (BigWittLaw.hasSubst_addFam R)
    hasSubst_ahFam constantCoeff_ahFam
    (fun m => MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R m) hG.1 hG.2).1
  subst_eq := (precomp_hom (Φ := Φ) (WittLaw.hasSubst_addFam p R) (BigWittLaw.hasSubst_addFam R)
    hasSubst_ahFam constantCoeff_ahFam
    (fun m => MvFormalGroup.ArtinHasse.subst_addFam_map_coord p R m) hG.1 hG.2).2

theorem toPowerSeries_toCM (G : Fin d → MvPowerSeries ℕ R) (hG : IsLamHom Φ G) (j : Fin d) :
    (toCM (p := p) Φ G hG).toPowerSeries j = subst (ahFam p R) (G j) := rfl

theorem toCM_comp_proj : toCM (p := p) Φ _ (isLamHom_comp_proj (p := p) Φ f) = f := by
  refine CartierModule.ext (funext fun j => ?_)
  rw [toPowerSeries_toCM, subst_comp_subst_apply (BigWittLaw.hasSubst_projFam R hp.out.two_le) hasSubst_ahFam]
  have hid : (fun k => subst (ahFam p R) (MvFormalGroup.BigWittLaw.projFam R p k)) =
      fun k => (MvPowerSeries.X k : MvPowerSeries ℕ R) :=
    funext fun k => (MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam p R).2 k
  rw [hid]
  exact congrFun (subst_self (σ := ℕ) (R := R)) (f.toPowerSeries j)

theorem toCM_stepD (D : Fin d → MvPowerSeries ℕ R) {n : ℕ} (hn : 2 ≤ n) (hD : IsLamHom Φ D)
    (hD' : IsLamHom Φ (stepD (p := p) Φ D n)) :
    toCM (p := p) Φ (stepD (p := p) Φ D n) hD' =
      toCM (p := p) Φ D hD - toCM (p := p) Φ (HOf (p := p) Φ (cOf D n) n) (HOf_isLamHom (p := p) Φ _ hn) := by
  refine CartierModule.ext (funext fun j => ?_)
  rw [toPowerSeries_sub, toPowerSeries_toCM]
  show subst (ahFam p R) (subst (Sum.elim D (negSeries Φ (HOf (p := p) Φ (cOf D n) n))) (Φ.toPowerSeries j)) = _
  rw [subst_subst_elim Φ hD.1 (constantCoeff_negSeries Φ _) hasSubst_ahFam]
  congr 2
  exact subst_negSeries' Φ (HOf_isLamHom (p := p) Φ _ hn).1 hasSubst_ahFam constantCoeff_ahFam

end Seq

section Final
variable [Algebra ℤ_[p] R] (Φ : MvFormalGroup d R) [Φ.IsComm] (f : CartierModule p Φ)

omit hp in
theorem hasSubst_of_WV {w : ℕ → ℕ} {u : ℕ → MvPowerSeries ℕ R}
    (hu : ∀ i, WV w (i + 1) (u i)) : HasSubst u := by
  refine ⟨fun i => ?_, fun e => ?_⟩
  · have : MvPowerSeries.constantCoeff (u i) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; exact hu i 0 (by simp)
    rw [this]; exact IsNilpotent.zero
  · refine (Set.finite_le_nat (Finsupp.weight w e)).subset fun i hi => ?_
    show i ≤ Finsupp.weight w e
    by_contra hlt
    exact hi (hu i e (by omega))

theorem WV_projAH (i : ℕ) :
    WV (fun m : ℕ => m + 1) (i + 1)
      (subst (MvFormalGroup.BigWittLaw.projFam R p) (ahFam p R i)) := by
  refine WV.subst_of_raise (w := fun k : ℕ => p ^ k) (BigWittLaw.hasSubst_projFam R hp.out.two_le)
    (fun k => ?_) (WV_ahFam i)
  intro e he
  by_contra h
  have := BigWittLaw.weight_eq_of_coeff_toFam_ne_zero R
    (BigWittLaw.isWeightedHomogeneous_projPoly hp.out.pos k) h
  exact absurd he (by rw [show Finsupp.weight (fun m : ℕ => m + 1) e = p ^ k from this]; exact lt_irrefl _)

theorem subst_ahFam_frobFam_eq_zero (m : ℕ) (hm : ¬ ∃ k : ℕ, m = p ^ k) (k : ℕ) :
    subst (ahFam p R) (MvFormalGroup.BigWittLaw.frobFam R m k) = 0 := by
  have hK2a := (MvFormalGroup.BigWittLaw.subst_addFam_projFam_and_subst_artinHasse_projFam p R).2
  have hK2b := (MvFormalGroup.BigWittLaw.subst_artinHasse_projFam_frobFam p R).1 m hm k

  have he : HasSubst (fun i => subst (MvFormalGroup.BigWittLaw.projFam R p) (ahFam p R i)) :=
    hasSubst_of_WV (fun i => WV_projAH (p := p) (R := R) i)
  have hαe : (fun i => subst (ahFam p R) (subst (MvFormalGroup.BigWittLaw.projFam R p) (ahFam p R i))) =
      ahFam p R := by
    funext i
    rw [subst_comp_subst_apply (BigWittLaw.hasSubst_projFam R hp.out.two_le) hasSubst_ahFam]
    have hid : (fun l => subst (ahFam p R) (MvFormalGroup.BigWittLaw.projFam R p l)) =
        fun l => (MvPowerSeries.X l : MvPowerSeries ℕ R) := funext fun l => hK2a l
    rw [hid]
    exact congrFun (subst_self (σ := ℕ) (R := R)) _
  have hK2b' : subst (fun i => subst (MvFormalGroup.BigWittLaw.projFam R p) (ahFam p R i))
      (MvFormalGroup.BigWittLaw.frobFam R m k) = 0 := hK2b
  have := congrArg (subst (ahFam p R)) hK2b'
  rw [subst_comp_subst_apply he hasSubst_ahFam, hαe, ← coe_substAlgHom hasSubst_ahFam, map_zero,
    coe_substAlgHom] at this
  exact this

theorem main (hf : tangent f = 0) : ∃ g : CartierModule p Φ, verschiebungInt g = f := by
  classical
  have h2p : 2 ≤ p := hp.out.two_le
  have hspec := Dseq_spec (p := p) Φ f hf

  let c : ℕ → Fin d → R := fun i => cOf (Dseq (p := p) Φ f i) (i + 2)
  let 𝔡 : ℕ → CartierModule p Φ := fun i => toCM (p := p) Φ (Dseq (p := p) Φ f i) (hspec i).1
  let 𝔥 : ℕ → CartierModule p Φ := fun i =>
    toCM (p := p) Φ (HOf (p := p) Φ (c i) (i + 2)) (HOf_isLamHom (p := p) Φ _ (by omega))
  let 𝔢 : ℕ → CartierModule p Φ := fun i => toCM (p := p) Φ (EOf (p := p) Φ (c i) (i + 2)) (EOf_isLamHom (p := p) Φ _ _)

  have hC3 : ∀ n, 𝔡 n = f - ∑ i ∈ Finset.range n, 𝔥 i := by
    intro n
    induction n with
    | zero =>
      rw [Finset.sum_range_zero, sub_zero]
      exact toCM_comp_proj (p := p) Φ f
    | succ n ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ← ih]
      exact toCM_stepD (p := p) Φ (Dseq (p := p) Φ f n) (by omega) (hspec n).1 (hspec (n + 1)).1

  have hC4 : ∀ i, (¬ ∃ k : ℕ, i + 2 = p ^ k) → 𝔥 i = 0 := by
    intro i hi
    have hq : qOf p (i + 2) = i + 2 := by unfold qOf; rw [if_neg hi]
    refine CartierModule.ext (funext fun j => ?_)
    show subst (ahFam p R) (subst (MvFormalGroup.BigWittLaw.frobFam R (qOf p (i + 2)))
      (EOf (p := p) Φ (c i) (i + 2) j)) = 0
    rw [subst_comp_subst_apply (BigWittLaw.hasSubst_frobFam R _) hasSubst_ahFam, hq]
    have h0 : (fun m => subst (ahFam p R) (MvFormalGroup.BigWittLaw.frobFam R (i + 2) m)) =
        fun _ => (0 : MvPowerSeries ℕ R) := funext fun m => subst_ahFam_frobFam_eq_zero (p := p) (R := R) (i + 2) hi m
    rw [h0]
    exact subst_zero_family _ ((EOf_isLamHom (p := p) Φ (c i) (i + 2)).1 j)

  have hC5 : ∀ i, (∃ k : ℕ, i + 2 = p ^ k) → 𝔥 i = verschiebungInt (𝔢 i) := by
    intro i hi
    have hq : qOf p (i + 2) = p := by unfold qOf; rw [if_pos hi]
    refine CartierModule.ext (funext fun j => ?_)
    show subst (ahFam p R) (subst (MvFormalGroup.BigWittLaw.frobFam R (qOf p (i + 2)))
      (EOf (p := p) Φ (c i) (i + 2) j)) =
      subst (frobPolyFam p R) (subst (ahFam p R) (EOf (p := p) Φ (c i) (i + 2) j))
    rw [subst_comp_subst_apply (BigWittLaw.hasSubst_frobFam R _) hasSubst_ahFam, hq,
      subst_comp_subst_apply hasSubst_ahFam hasSubst_frobPolyFam]
    congr 1
    funext m
    exact MvFormalGroup.BigWittLaw.subst_artinHasse_frobFam p R m

  have hC6 : ∀ (n : ℕ) (j : Fin d), WV (fun m : ℕ => p ^ m) (n + 2) ((𝔡 n).toPowerSeries j) := by
    intro n j
    show WV (fun m : ℕ => p ^ m) (n + 2) (subst (ahFam p R) (Dseq (p := p) Φ f n j))
    refine WV.subst_of_raise (w := fun m : ℕ => m + 1) hasSubst_ahFam (fun m => WV_ahFam m) ?_
    intro e he
    exact MvFormalGroup.BigWittLaw.coeff_eq_zero_of_coeff_subst_pow_eq_zero Φ _ (hspec n).1.1 (hspec n).1.2
      (n + 2) (hspec n).2 j e he

  have hC7 : ∀ (i : ℕ) (j : Fin d), WV (fun m : ℕ => p ^ m) (rOf p (i + 2)) ((𝔢 i).toPowerSeries j) := by
    intro i j
    show WV (fun m : ℕ => p ^ m) (rOf p (i + 2)) (subst (ahFam p R) (EOf (p := p) Φ (c i) (i + 2) j))
    refine WV.subst_of_raise (w := fun m : ℕ => m + 1) hasSubst_ahFam (fun m => WV_ahFam m) ?_
    intro e he
    refine MvFormalGroup.BigWittLaw.coeff_eq_zero_of_coeff_subst_pow_eq_zero Φ _
      (EOf_isLamHom (p := p) Φ (c i) (i + 2)).1 (EOf_isLamHom (p := p) Φ (c i) (i + 2)).2
      (rOf p (i + 2)) (fun j' k hk => ?_) j e he
    rw [omg_EOf, PowerSeries.coeff_monomial, if_neg (by omega)]

  let t : ℕ → CartierModule p Φ := fun k => 𝔢 (p ^ (k + 1) - 2)
  have hidx : ∀ k : ℕ, p ^ (k + 1) - 2 + 2 = p ^ (k + 1) := fun k =>
    Nat.sub_add_cancel (le_trans h2p (Nat.le_self_pow (Nat.succ_ne_zero k) p))
  obtain ⟨g, hg⟩ := MvFormalGroup.CartierModule.exists_forall_coeff_sub_sum_eq_zero p Φ t
    (fun k => p ^ k) (fun a b hab => Nat.pow_le_pow_right hp.out.pos hab)
    (fun B => ⟨B, (Nat.lt_pow_self hp.out.one_lt).le⟩)
    (fun k j e he => by
      have h7 := hC7 (p ^ (k + 1) - 2) j
      rw [hidx, rOf_ppow] at h7
      exact h7 e he)
  refine ⟨g, ?_⟩

  refine CartierModule.ext (funext fun j => ?_)
  ext e
  set K : ℕ := Finsupp.weight (fun m : ℕ => p ^ m) e + 1 with hKdef
  have hK : Finsupp.weight (fun m : ℕ => p ^ m) e < p ^ K :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (by rw [hKdef]; exact (Nat.lt_pow_self hp.out.one_lt).le)

  have hVrem : ∀ j', WV (fun m : ℕ => p ^ m) (p ^ K)
      ((verschiebungInt (g - ∑ k ∈ Finset.range K, t k)).toPowerSeries j') := by
    intro j'
    show WV (fun m : ℕ => p ^ m) (p ^ K)
      (subst (frobPolyFam p R) ((g - ∑ k ∈ Finset.range K, t k).toPowerSeries j'))
    refine WV.subst_of_raise (w := fun m : ℕ => p ^ m) hasSubst_frobPolyFam (fun n => ?_)
      (fun e' he' => hg K j' e' he')
    intro e' he'
    by_contra h
    have h1 := weight_eq_of_coeff_frobPolyFam_ne_zero h
    have h2 : p ^ n ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.out.pos (Nat.le_succ n)
    omega

  have hVg : verschiebungInt g =
      (∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2)) + verschiebungInt (g - ∑ k ∈ Finset.range K, t k) := by
    have hAB : ∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2) =
        ∑ k ∈ Finset.range K, verschiebungInt (t k) :=
      Finset.sum_congr rfl fun k _ => hC5 _ ⟨k + 1, hidx k⟩
    rw [hAB, map_sub, map_sum]
    abel

  have hf' : f = (∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2)) + 𝔡 (p ^ K - 1) := by
    have h3 := hC3 (p ^ K - 1)
    have hsum : ∑ i ∈ Finset.range (p ^ K - 1), 𝔥 i = ∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ K - 1))
        (fun i => ∃ k : ℕ, i + 2 = p ^ k)]
      rw [Finset.sum_eq_zero (s := Finset.filter (fun i => ¬ ∃ k : ℕ, i + 2 = p ^ k) (Finset.range (p ^ K - 1)))
        (fun i hi => hC4 i (Finset.mem_filter.mp hi).2), add_zero]
      have hset : (Finset.range (p ^ K - 1)).filter (fun i => ∃ k : ℕ, i + 2 = p ^ k) =
          (Finset.range K).image (fun k => p ^ (k + 1) - 2) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hi, k', hk'⟩
          have hk'0 : k' ≠ 0 := by
            rintro rfl
            rw [pow_zero] at hk'
            omega
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk'0
          rw [Nat.succ_eq_add_one] at hk'
          refine ⟨k, ?_, by omega⟩
          have hle : p ^ (k + 1) ≤ p ^ K := by omega
          have := (Nat.pow_le_pow_iff_right h2p).mp hle
          omega
        · rintro ⟨k, hk, rfl⟩
          have hle : p ^ (k + 1) ≤ p ^ K := Nat.pow_le_pow_right hp.out.pos (by omega)
          have := hidx k
          exact ⟨by omega, k + 1, hidx k⟩
      rw [hset, Finset.sum_image]
      intro k₁ _ k₂ _ h
      dsimp only at h
      have h' : p ^ (k₁ + 1) = p ^ (k₂ + 1) := by
        have := hidx k₁; have := hidx k₂; omega
      have := Nat.pow_right_injective h2p h'
      omega
    rw [h3, hsum]
    abel

  have e1 : Cong (p ^ K) (verschiebungInt g) (∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2)) := by
    rw [hVg]
    exact Cong.add_small _ hVrem
  have e2 : Cong (p ^ K) f (∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2)) := by
    have hsmall : ∀ j', WV (fun m : ℕ => p ^ m) (p ^ K) ((𝔡 (p ^ K - 1)).toPowerSeries j') :=
      fun j' => (hC6 (p ^ K - 1) j').mono (by omega)
    have := Cong.add_small (∑ k ∈ Finset.range K, 𝔥 (p ^ (k + 1) - 2)) hsmall
    rw [← hf'] at this
    exact this
  have e3 := (e1.trans e2.symm) j e hK
  rw [map_sub, sub_eq_zero] at e3
  exact e3

end Final

end B23K5

end

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (f : MvFormalGroup.CartierModule p Φ)
    (hf : MvFormalGroup.CartierModule.tangent f = 0) :
    ∃ g : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f :=
  B23K5.main (p := p) Φ f hf

end S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt (solution)
