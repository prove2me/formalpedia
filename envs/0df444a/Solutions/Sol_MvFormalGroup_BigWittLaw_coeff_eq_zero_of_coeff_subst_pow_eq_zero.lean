-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.coeff_eq_zero_of_coeff_subst_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/93c3021c-f031-5f89-b52c-f644cceb080a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "coeff_finsuppProd_pow_eq_zero_of_degree_lt negSeries negSeries_unique invSeries constantCoeff_invSeries subst_negSeries map mk toPowerSeries constantCoeff_eq_zero CartierModule CartierModule.curveFam CartierModule.constantCoeff_curveFam CartierModule.hasSubst_curveFam BigWittLaw.addFam BigWittLaw.addFam_eq BigWittLaw.hasSubst_addFam"
namespace BigWittLaw
p2m_export "MvFormalGroup.BigWittLaw" "addFam addFam_eq hasSubst_addFam awt"
namespace K0q
p2m_open "MvFormalGroup.BigWittLaw MvFormalGroup"

variable (N : ℕ) (R : Type u) [CommRing R]

def esymmFam : ℕ → MvPowerSeries (Fin N) R :=
  fun m => ((MvPolynomial.esymm (Fin N) R (m + 1) : MvPolynomial (Fin N) R) : MvPowerSeries (Fin N) R)

theorem coeff_esymmFam (m : ℕ) (s : Fin N →₀ ℕ) :
    coeff s (esymmFam N R m) = MvPolynomial.coeff s (MvPolynomial.esymm (Fin N) R (m + 1)) := by
  rw [esymmFam, MvPolynomial.coeff_coe]

theorem esymm_eq_zero_of_lt {k : ℕ} (h : N < k) : MvPolynomial.esymm (Fin N) R k = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr (by simpa using h), Finset.sum_empty]

theorem esymmFam_eq_zero_of_le {m : ℕ} (h : N ≤ m) : esymmFam N R m = 0 := by
  rw [esymmFam, esymm_eq_zero_of_lt N R (by omega), MvPolynomial.coe_zero]

theorem isHomogeneous_esymm (k : ℕ) : (MvPolynomial.esymm (Fin N) R k).IsHomogeneous k := by
  rw [MvPolynomial.esymm_eq_sum_monomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_sum]
  simp only [Finsupp.degree_single, Finset.sum_const, smul_eq_mul, mul_one]
  exact (Finset.mem_powersetCard.mp ht).2

theorem coeff_esymmFam_eq_zero {m : ℕ} {s : Fin N →₀ ℕ} (hs : s.degree ≠ m + 1) :
    coeff s (esymmFam N R m) = 0 := by
  rw [coeff_esymmFam]
  exact (isHomogeneous_esymm N R (m + 1)).coeff_eq_zero hs

theorem constantCoeff_esymmFam (m : ℕ) : constantCoeff (esymmFam N R m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_esymmFam_eq_zero N R (by rw [map_zero]; omega)

theorem hasSubst_esymmFam : HasSubst (esymmFam N R) := by
  refine ⟨fun m => by rw [constantCoeff_esymmFam]; exact IsNilpotent.zero, fun s => ?_⟩
  refine (Set.finite_lt_nat N).subset fun m hm => ?_
  by_contra hNm
  exact hm (by rw [esymmFam_eq_zero_of_le N R (Nat.not_lt.mp hNm), map_zero])

abbrev awt : ℕ → ℕ := fun m => m + 1

theorem coeff_prod_esymmFam_eq_zero (e : ℕ →₀ ℕ) {s : Fin N →₀ ℕ}
    (hs : s.degree ≠ Finsupp.weight awt e) :
    coeff s (e.prod fun m k => esymmFam N R m ^ k) = 0 := by
  have hpoly : (e.prod fun m k => esymmFam N R m ^ k)
      = ((e.prod fun m k => MvPolynomial.esymm (Fin N) R (m + 1) ^ k : MvPolynomial (Fin N) R) :
          MvPowerSeries (Fin N) R) := by
    have hc : ∀ P : MvPolynomial (Fin N) R,
        (P : MvPowerSeries (Fin N) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl
    rw [Finsupp.prod, Finsupp.prod, hc, map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [map_pow, ← hc]
    rfl
  rw [hpoly, MvPolynomial.coeff_coe]
  apply MvPolynomial.IsHomogeneous.coeff_eq_zero _ hs
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  apply MvPolynomial.IsHomogeneous.prod
  intro m _
  simpa [smul_eq_mul, mul_comm] using (isHomogeneous_esymm N R (m + 1)).pow (e m)

def gFam : Fin N → MvPowerSeries (Fin N) R :=
  fun i => ((MvPolynomial.esymm (Fin N) R (i.val + 1) : MvPolynomial (Fin N) R) : MvPowerSeries (Fin N) R)

abbrev fwt : Fin N → ℕ := fun i => i.val + 1

theorem hasSubst_gFam : HasSubst (gFam N R) :=
  hasSubst_of_constantCoeff_zero fun i => by
    rw [gFam, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact (isHomogeneous_esymm N R _).coeff_eq_zero (by rw [map_zero]; omega)

theorem prod_gFam_eq_coe (f : Fin N →₀ ℕ) :
    (f.prod fun i k => gFam N R i ^ k)
      = ((f.prod fun i k => MvPolynomial.esymm (Fin N) R (i.val + 1) ^ k : MvPolynomial (Fin N) R) :
          MvPowerSeries (Fin N) R) := by
  have hc : ∀ P : MvPolynomial (Fin N) R,
      (P : MvPowerSeries (Fin N) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl
  rw [Finsupp.prod, Finsupp.prod, hc, map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [map_pow, ← hc]
  rfl

theorem isHomogeneous_prod_esymm (f : Fin N →₀ ℕ) :
    (f.prod fun i k => MvPolynomial.esymm (Fin N) R (i.val + 1) ^ k : MvPolynomial (Fin N) R).IsHomogeneous
      (Finsupp.weight (fwt N) f) := by
  rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  apply MvPolynomial.IsHomogeneous.prod
  intro m _
  simpa [smul_eq_mul, mul_comm] using (isHomogeneous_esymm N R (m.val + 1)).pow (f m)

theorem coeff_subst_gFam (Q : MvPowerSeries (Fin N) R) (s : Fin N →₀ ℕ) (F : Finset (Fin N →₀ ℕ))
    (hF : ∀ f : Fin N →₀ ℕ, Finsupp.weight (fwt N) f = s.degree → f ∈ F) :
    coeff s (subst (gFam N R) Q)
      = MvPolynomial.coeff s (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) R (i.val + 1))
          (∑ f ∈ F, MvPolynomial.monomial f (coeff f Q))) := by
  classical
  rw [coeff_subst (hasSubst_gFam N R)]
  have hsupp : Function.support (fun f : Fin N →₀ ℕ => coeff f Q • coeff s (f.prod fun i k => gFam N R i ^ k))
      ⊆ (F : Set (Fin N →₀ ℕ)) := by
    intro f hf
    rw [Function.mem_support] at hf
    apply hF
    by_contra hne
    apply hf
    rw [prod_gFam_eq_coe, MvPolynomial.coeff_coe,
      (isHomogeneous_prod_esymm N R f).coeff_eq_zero (fun h => hne h.symm), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul, prod_gFam_eq_coe,
    MvPolynomial.coeff_coe, smul_eq_mul]

theorem coeff_eq_zero_of_coeff_subst_gFam_eq_zero (Q : MvPowerSeries (Fin N) R) (w : ℕ)
    (h : ∀ s : Fin N →₀ ℕ, s.degree = w → coeff s (subst (gFam N R) Q) = 0)
    (f : Fin N →₀ ℕ) (hf : Finsupp.weight (fwt N) f = w) : coeff f Q = 0 := by
  classical

  set F : Finset (Fin N →₀ ℕ) :=
    ((Finset.range (w + 1)).biUnion fun dd => (Finset.univ : Finset (Fin N)).finsuppAntidiag dd).filter
      (fun f => Finsupp.weight (fwt N) f = w) with hFdef
  have hF : ∀ g : Fin N →₀ ℕ, Finsupp.weight (fwt N) g = w → g ∈ F := by
    intro g hg
    rw [hFdef, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ⟨g.degree, ?_, ?_⟩, hg⟩
    · rw [Finset.mem_range]
      have : g.degree ≤ Finsupp.weight (fwt N) g := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Finsupp.weight_apply]
        exact Finsupp.sum_le_sum fun i _ => by
          simp only [fwt, smul_eq_mul, mul_one]
          exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    · rw [Finset.mem_finsuppAntidiag]
      exact ⟨(Finsupp.degree_eq_sum g).symm, Finset.subset_univ _⟩

  set T : MvPolynomial (Fin N) R := ∑ g ∈ F, MvPolynomial.monomial g (coeff g Q) with hT
  have hcoeffT : ∀ s : Fin N →₀ ℕ, MvPolynomial.coeff s
      (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) R (i.val + 1)) T) = 0 := by
    intro s
    by_cases hs : s.degree = w
    · rw [← coeff_subst_gFam N R Q s F (fun g hg => hF g (by rw [hg, hs]))]
      exact h s hs
    · have hhom : (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) R (i.val + 1)) T).IsHomogeneous w := by
        rw [hT, map_sum]
        apply MvPolynomial.IsHomogeneous.sum
        intro g hg
        have hgw : Finsupp.weight (fwt N) g = w := (Finset.mem_filter.mp hg).2
        rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, ← zero_add w, ← hgw]
        exact (MvPolynomial.isHomogeneous_C _ _).mul (isHomogeneous_prod_esymm N R g)
      exact hhom.coeff_eq_zero hs
  have hTeval : MvPolynomial.esymmAlgHom (Fin N) R N T = 0 := by
    apply Subtype.ext
    rw [MvPolynomial.esymmAlgHom_apply]
    ext s
    rw [hcoeffT]
    simp
  have hT0 : T = 0 := MvPolynomial.esymmAlgHom_fin_injective R le_rfl (by rw [hTeval, map_zero])
  have hread : MvPolynomial.coeff f T = coeff f Q := by
    rw [hT, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq', if_pos (hF f hf)]
  rw [← hread, hT0, MvPolynomial.coeff_zero]

theorem esymm_succ_fin (k : ℕ) :
    MvPolynomial.esymm (Fin (N + 1)) R (k + 1)
      = MvPolynomial.rename Fin.castSucc (MvPolynomial.esymm (Fin N) R (k + 1))
        + MvPolynomial.X (Fin.last N) * MvPolynomial.rename Fin.castSucc (MvPolynomial.esymm (Fin N) R k) := by
  classical
  have hren : ∀ n, MvPolynomial.rename Fin.castSucc (MvPolynomial.esymm (Fin N) R n)
      = ∑ t ∈ Finset.powersetCard n (Finset.univ.map Fin.castSuccEmb), ∏ i ∈ t, MvPolynomial.X i := by
    intro n
    rw [MvPolynomial.esymm, map_sum, Finset.powersetCard_map, Finset.sum_map]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_prod]
    change ∏ x ∈ t, (MvPolynomial.rename Fin.castSucc) (MvPolynomial.X x) = ∏ i ∈ t.map Fin.castSuccEmb, MvPolynomial.X i
    rw [Finset.prod_map]
    simp [MvPolynomial.rename_X]
  rw [MvPolynomial.esymm, Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.powersetCard_succ_insert (by simp),
    Finset.sum_union, hren, hren, Finset.sum_image, Finset.mul_sum]
  · congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_insert]
    intro hmem
    have := (Finset.mem_powersetCard.mp ht).1 hmem
    simp at this
  ·
    intro t ht t' ht' h
    have hl : Fin.last N ∉ t := fun hm => by simpa using (Finset.mem_powersetCard.mp ht).1 hm
    have hl' : Fin.last N ∉ t' := fun hm => by simpa using (Finset.mem_powersetCard.mp ht').1 hm
    rw [← Finset.erase_insert hl, ← Finset.erase_insert hl', h]
  ·
    rw [Finset.disjoint_left]
    intro t ht himg
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp himg
    have := (Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _)
    simp at this

section UpTo

variable (M : ℕ)

def esymmUpTo (N k : ℕ) : MvPolynomial (Fin M) R :=
  ∑ t ∈ Finset.powersetCard k ((Finset.univ : Finset (Fin M)).filter fun i => i.val < N), ∏ i ∈ t, MvPolynomial.X i

theorem esymmUpTo_zero_left (k : ℕ) : esymmUpTo R M 0 (k + 1) = 0 := by
  classical
  rw [esymmUpTo, Finset.powersetCard_eq_empty.mpr, Finset.sum_empty]
  simp

theorem esymmUpTo_eq_zero_of_lt {N k : ℕ} (h : N < k) : esymmUpTo R M N k = 0 := by
  classical
  rw [esymmUpTo, Finset.powersetCard_eq_empty.mpr, Finset.sum_empty]
  calc ((Finset.univ : Finset (Fin M)).filter fun i => i.val < N).card
      ≤ (Finset.range N).card := by
        refine Finset.card_le_card_of_injOn (fun i => i.val) (fun i hi => ?_) (fun a _ b _ h => Fin.ext h)
        simpa using (Finset.mem_filter.mp hi).2
    _ = N := Finset.card_range N
    _ < k := h

theorem esymmUpTo_top (k : ℕ) : esymmUpTo R M M k = MvPolynomial.esymm (Fin M) R k := by
  classical
  have hf : ((Finset.univ : Finset (Fin M)).filter fun i => i.val < M) = Finset.univ := by
    ext i
    simp [i.isLt]
  rw [esymmUpTo, hf, MvPolynomial.esymm]

theorem esymmUpTo_zero_right (N : ℕ) : esymmUpTo R M N 0 = 1 := by
  classical
  rw [esymmUpTo, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

theorem esymmUpTo_succ {N : ℕ} (hN : N < M) (k : ℕ) :
    esymmUpTo R M (N + 1) (k + 1)
      = esymmUpTo R M N (k + 1) + MvPolynomial.X (⟨N, hN⟩ : Fin M) * esymmUpTo R M N k := by
  classical
  have hfilt : ((Finset.univ : Finset (Fin M)).filter fun i => i.val < N + 1)
      = insert (⟨N, hN⟩ : Fin M) ((Finset.univ : Finset (Fin M)).filter fun i => i.val < N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨N, hN⟩ : Fin M) ∉ ((Finset.univ : Finset (Fin M)).filter fun i => i.val < N) := by simp
  rw [esymmUpTo, hfilt, Finset.powersetCard_succ_insert hnot, Finset.sum_union, esymmUpTo, esymmUpTo,
    Finset.sum_image, Finset.mul_sum]
  · congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_insert]
    exact fun hm => hnot ((Finset.mem_powersetCard.mp ht).1 hm)
  · intro t ht t' ht' h
    have hl : (⟨N, hN⟩ : Fin M) ∉ t := fun hm => hnot ((Finset.mem_powersetCard.mp ht).1 hm)
    have hl' : (⟨N, hN⟩ : Fin M) ∉ t' := fun hm => hnot ((Finset.mem_powersetCard.mp ht').1 hm)
    rw [← Finset.erase_insert hl, ← Finset.erase_insert hl', h]
  · rw [Finset.disjoint_left]
    intro t ht himg
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp himg
    exact hnot ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))

def upFam (N : ℕ) : ℕ → MvPowerSeries (Fin M) R := fun m => (esymmUpTo R M N (m + 1) : MvPowerSeries (Fin M) R)

end UpTo

section Vanish

variable {σ τ : Type*}

omit N in
theorem coeff_pow_eq_zero_of_lt' {g : MvPowerSeries τ R} {K : ℕ}
    (hg : ∀ s : τ →₀ ℕ, s.degree < K → coeff s g = 0) {L : ℕ} {s : τ →₀ ℕ}
    (hs : s.degree < K * L) : coeff s (g ^ L) = 0 := by
  classical
  induction L generalizing s with
  | zero => simp at hs
  | succ L IH =>
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdd : q.1.degree + q.2.degree = s.degree := by rw [← hq, map_add]
    by_cases h1 : q.1.degree < K * L
    · rw [IH h1, zero_mul]
    · have h2 : q.2.degree < K := by rw [Nat.mul_succ] at hs; omega
      rw [hg q.2 h2, mul_zero]

omit N in

theorem coeff_subst_eq_zero_of_lt (a : σ → MvPowerSeries τ R) (ha : HasSubst a) (K : ℕ)
    (hK : ∀ (i : σ) (s : τ →₀ ℕ), s.degree < K → coeff s (a i) = 0)
    (F : MvPowerSeries σ R) (hF : constantCoeff F = 0)
    (s : τ →₀ ℕ) (hs : s.degree < K) : coeff s (subst a F) = 0 := by
  classical
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, coeff_zero_eq_constantCoeff_apply, hF, zero_smul]
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push Not at h
      exact he (Finsupp.ext h)
    have hsplit : (e.prod fun j k => a j ^ k) = a i ^ e i * (e.erase i).prod fun j k => a j ^ k := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.support_erase, ← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.mpr hi)]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hj)]
    have hvan : coeff s (e.prod fun j k => a j ^ k) = 0 := by
      rw [hsplit, coeff_mul]
      refine Finset.sum_eq_zero fun q hq => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      have hdd : q.1.degree + q.2.degree = s.degree := by rw [← hq, map_add]
      have h1 : q.1.degree < K * e i := by
        calc q.1.degree ≤ s.degree := by omega
          _ < K := hs
          _ ≤ K * e i := Nat.le_mul_of_pos_right K (Nat.pos_of_ne_zero hi)
      rw [coeff_pow_eq_zero_of_lt' R (hK i) h1, zero_mul]
    rw [hvan, smul_zero]

end Vanish

section OneVar

variable (M : ℕ)

def oneVarFam (n : Fin M) : ℕ → MvPowerSeries (Fin M) R
  | 0 => MvPowerSeries.X n
  | _ + 1 => 0

theorem hasSubst_oneVarFam (n : Fin M) : HasSubst (oneVarFam R M n) := by
  refine ⟨fun k => ?_, fun s => ?_⟩
  · cases k with
    | zero => rw [oneVarFam, constantCoeff_X]; exact IsNilpotent.zero
    | succ k => rw [oneVarFam, map_zero]; exact IsNilpotent.zero
  · refine (Set.finite_singleton 0).subset fun k hk => ?_
    cases k with
    | zero => rfl
    | succ k => exact absurd (by rw [oneVarFam, map_zero]) hk

theorem oneVarFam_eq (n : Fin M) :
    oneVarFam R M n = fun k => subst (fun _ : Unit => (MvPowerSeries.X n : MvPowerSeries (Fin M) R))
      (MvFormalGroup.CartierModule.curveFam R k) := by
  funext k
  have hX : HasSubst (fun _ : Unit => (MvPowerSeries.X n : MvPowerSeries (Fin M) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  cases k with
  | zero =>
    show (MvPowerSeries.X n : MvPowerSeries (Fin M) R) = subst _ (PowerSeries.X)
    rw [show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, subst_X hX]
  | succ k =>
    show (0 : MvPowerSeries (Fin M) R) = subst _ 0
    rw [← coe_substAlgHom hX, map_zero]

theorem coeff_subst_oneVarFam_eq_zero (n : Fin M) (G : MvPowerSeries ℕ R) (K : ℕ)
    (hγ : ∀ k : ℕ, k < K → PowerSeries.coeff k (subst (MvFormalGroup.CartierModule.curveFam R) G) = 0)
    (s : Fin M →₀ ℕ) (hs : s.degree < K) : coeff s (subst (oneVarFam R M n) G) = 0 := by
  classical
  have hX : HasSubst (fun _ : Unit => (MvPowerSeries.X n : MvPowerSeries (Fin M) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  rw [oneVarFam_eq, ← subst_comp_subst_apply (MvFormalGroup.CartierModule.hasSubst_curveFam (R := R)) hX]

  set emb : Unit ↪ Fin M := ⟨fun _ => n, fun _ _ _ => rfl⟩ with hemb
  haveI : Filter.TendstoCofinite (⇑emb) := Filter.tendstoCofinite_of_injective emb.injective
  have hren : subst (fun _ : Unit => (MvPowerSeries.X n : MvPowerSeries (Fin M) R))
      (subst (MvFormalGroup.CartierModule.curveFam R) G)
      = rename (⇑emb) (subst (MvFormalGroup.CartierModule.curveFam R) G) := by
    rw [rename_eq_subst]
    rfl
  rw [hren]
  by_cases hr : s ∈ Set.range (Finsupp.mapDomain (⇑emb))
  · obtain ⟨x, rfl⟩ := hr
    have hx : x = Finsupp.single () (x ()) := by ext u; simp
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    rw [hx, Finsupp.mapDomain_single, Finsupp.degree_single] at hs
    rw [hx]
    exact hγ (x ()) hs
  · exact coeff_rename_eq_zero _ _ hr

end OneVar

section Induction

variable (M : ℕ)

theorem isHomogeneous_esymmUpTo (N k : ℕ) : (esymmUpTo R M N k).IsHomogeneous k := by
  classical
  rw [esymmUpTo]
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  have hcard : t.card = k := (Finset.mem_powersetCard.mp ht).2
  have := MvPolynomial.IsHomogeneous.prod t (fun i => (MvPolynomial.X i : MvPolynomial (Fin M) R)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X R i)
  rwa [Finset.sum_const, smul_eq_mul, mul_one, hcard] at this

theorem constantCoeff_upFam (N m : ℕ) : constantCoeff (upFam R M N m) = 0 := by
  rw [upFam, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  exact (isHomogeneous_esymmUpTo R M N (m + 1)).coeff_eq_zero (by rw [map_zero]; omega)

theorem upFam_eq_zero_of_le {N m : ℕ} (h : N ≤ m) : upFam R M N m = 0 := by
  rw [upFam, esymmUpTo_eq_zero_of_lt R M (by omega), MvPolynomial.coe_zero]

theorem hasSubst_upFam (N : ℕ) : HasSubst (upFam R M N) := by
  refine ⟨fun m => by rw [constantCoeff_upFam]; exact IsNilpotent.zero, fun s => ?_⟩
  refine (Set.finite_lt_nat N).subset fun m hm => ?_
  by_contra hNm
  exact hm (by rw [upFam_eq_zero_of_le R M (Nat.not_lt.mp hNm), map_zero])

def theta (N : ℕ) (hN : N < M) : Fin 2 × ℕ → MvPowerSeries (Fin M) R :=
  fun ik => if ik.1 = 0 then upFam R M N ik.2 else oneVarFam R M ⟨N, hN⟩ ik.2

theorem theta_zero (N : ℕ) (hN : N < M) (k : ℕ) : theta R M N hN (0, k) = upFam R M N k := if_pos rfl
theorem theta_one (N : ℕ) (hN : N < M) (k : ℕ) : theta R M N hN (1, k) = oneVarFam R M ⟨N, hN⟩ k :=
  if_neg (fun h => (one_ne_zero : (1 : Fin 2) ≠ 0) h)

theorem oneVarFam_zero (n : Fin M) : oneVarFam R M n 0 = MvPowerSeries.X n := rfl
theorem oneVarFam_succ (n : Fin M) (k : ℕ) : oneVarFam R M n (k + 1) = 0 := rfl
theorem oneVarFam_of_ne_zero (n : Fin M) {k : ℕ} (hk : k ≠ 0) : oneVarFam R M n k = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rfl

theorem hasSubst_theta (N : ℕ) (hN : N < M) : HasSubst (theta R M N hN) := by
  classical
  refine ⟨fun ik => ?_, fun s => ?_⟩
  · rcases ik with ⟨i, k⟩
    by_cases hi : i = 0
    · subst hi; rw [theta_zero, constantCoeff_upFam]; exact IsNilpotent.zero
    · rw [show i = 1 by omega, theta_one]
      exact (hasSubst_oneVarFam R M ⟨N, hN⟩).const_coeff k
  · refine (((Finset.univ : Finset (Fin 2)) ×ˢ Finset.range (N + 1)).finite_toSet).subset fun ik hik => ?_
    rcases ik with ⟨i, k⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and, Finset.mem_range]
    by_contra hk
    apply hik
    by_cases hi : i = 0
    · subst hi; rw [theta_zero, upFam_eq_zero_of_le R M (by omega), map_zero]
    · rw [show i = 1 by omega, theta_one, oneVarFam_of_ne_zero R M _ (by omega), map_zero]

theorem subst_theta_addFam (N : ℕ) (hN : N < M) (m : ℕ) :
    subst (theta R M N hN) (MvFormalGroup.BigWittLaw.addFam R m) = upFam R M (N + 1) m := by
  classical
  have hθ := hasSubst_theta R M N hN
  rw [MvFormalGroup.BigWittLaw.addFam_eq, ← coe_substAlgHom hθ, map_add, map_add, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_X hθ, theta_zero, theta_one]
  have hc : ∀ P : MvPolynomial (Fin M) R,
      (P : MvPowerSeries (Fin M) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl
  cases m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, add_zero, oneVarFam_zero, upFam, upFam,
      esymmUpTo_succ R M hN 0, esymmUpTo_zero_right, mul_one, hc, hc, map_add, ← hc, ← hc, MvPolynomial.coe_X]
  | succ m' =>
    rw [oneVarFam_succ, add_zero, Finset.sum_eq_single_of_mem m' (Finset.mem_range.mpr (Nat.lt_succ_self m'))]
    · have h0 : m' + 1 - 1 - m' = 0 := by omega
      rw [h0, oneVarFam_zero, upFam, upFam, upFam, esymmUpTo_succ R M hN (m' + 1), hc, hc, hc,
        map_add, map_mul, ← hc, ← hc, ← hc, MvPolynomial.coe_X, mul_comm]
    · intro i hi hne
      rw [oneVarFam_of_ne_zero R M _ (by have := Finset.mem_range.mp hi; omega), mul_zero]

variable {d : ℕ} (Φ : MvFormalGroup d R)
variable (G : Fin d → MvPowerSeries ℕ R)
variable (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
variable (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
variable (K : ℕ)
variable (hγ : ∀ (j : Fin d) (n : ℕ), n < K →
      PowerSeries.coeff n (MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j)) = 0)

include hG0 hG hγ in

theorem coeff_subst_upFam_eq_zero :
    ∀ N : ℕ, N ≤ M → ∀ (j : Fin d) (s : Fin M →₀ ℕ), s.degree < K →
      coeff s (subst (upFam R M N) (G j)) = 0 := by
  classical
  intro N
  induction N with
  | zero =>
    intro _ j s hs
    have h0 : upFam R M 0 = fun _ => 0 := funext fun m => upFam_eq_zero_of_le R M (Nat.zero_le m)
    rw [h0]
    exact coeff_subst_eq_zero_of_lt R _ HasSubst.zero K (fun _ s' _ => by rw [map_zero]) (G j) (hG0 j) s hs
  | succ N IH =>
    intro hNM j s hs
    have hN : N < M := hNM
    have hθ := hasSubst_theta R M N hN
    have hfam : upFam R M (N + 1) = fun m => subst (theta R M N hN) (MvFormalGroup.BigWittLaw.addFam R m) :=
      funext fun m => (subst_theta_addFam R M N hN m).symm
    have hB0 : HasSubst (fun m : ℕ => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
      HasSubst.X_comp (Prod.mk 0)
    have hB1 : HasSubst (fun m : ℕ => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
      HasSubst.X_comp (Prod.mk 1)
    have hE : HasSubst (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l)
      · exact constantCoeff_subst_eq_zero hB0 (fun m => constantCoeff_X _) (hG0 l)
      · exact constantCoeff_subst_eq_zero hB1 (fun m => constantCoeff_X _) (hG0 l)
    rw [hfam, ← subst_comp_subst_apply (MvFormalGroup.BigWittLaw.hasSubst_addFam R) hθ, hG j,
      subst_comp_subst_apply hE hθ]
    have hfam2 : (fun x => subst (theta R M N hN) (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) x))
        = Sum.elim (fun l => subst (upFam R M N) (G l)) (fun l => subst (oneVarFam R M ⟨N, hN⟩) (G l)) := by
      funext x
      rcases x with l | l
      · show subst (theta R M N hN) (subst _ (G l)) = subst (upFam R M N) (G l)
        rw [subst_comp_subst_apply hB0 hθ]
        congr 1
        funext m
        rw [subst_X hθ, theta_zero]
      · show subst (theta R M N hN) (subst _ (G l)) = subst (oneVarFam R M ⟨N, hN⟩) (G l)
        rw [subst_comp_subst_apply hB1 hθ]
        congr 1
        funext m
        rw [subst_X hθ, theta_one]
    rw [hfam2]
    refine coeff_subst_eq_zero_of_lt R _ (hasSubst_of_constantCoeff_zero ?_) K ?_ (Φ.toPowerSeries j)
      (Φ.constantCoeff_eq_zero j) s hs
    · rintro (l | l)
      · exact constantCoeff_subst_eq_zero (hasSubst_upFam R M N) (constantCoeff_upFam R M N) (hG0 l)
      · exact constantCoeff_subst_eq_zero (hasSubst_oneVarFam R M _)
          (fun k => by cases k with
            | zero => exact constantCoeff_X _
            | succ k => exact map_zero _) (hG0 l)
    · rintro (l | l) s' hs'
      · exact IH hN.le l s' hs'
      · exact coeff_subst_oneVarFam_eq_zero R M ⟨N, hN⟩ (G l) K (hγ l) s' hs'

end Induction

section Final

variable (M : ℕ)

private abbrev _root_.MvFormalGroup.BigWittLaw.K0q.ext (f : Fin M →₀ ℕ) : ℕ →₀ ℕ := Finsupp.embDomain Fin.valEmbedding f

p2m_export "MvFormalGroup.BigWittLaw.K0q" "ext"
theorem prod_esymmFam_ext (f : Fin M →₀ ℕ) :
    ((ext M f).prod fun m k => esymmFam M R m ^ k) = f.prod fun i k => gFam M R i ^ k := by
  rw [ext, Finsupp.embDomain_eq_mapDomain,
    Finsupp.prod_mapDomain_index (h := fun m k => esymmFam M R m ^ k) (fun _ => pow_zero _)
      (fun _ _ _ => pow_add _ _ _)]
  rfl

theorem weight_ext (f : Fin M →₀ ℕ) : Finsupp.weight awt (ext M f) = Finsupp.weight (fwt M) f := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, ext, Finsupp.embDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (h := fun m c => c • awt m) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem prod_esymmFam_eq_zero_of_not_subset (e : ℕ →₀ ℕ)
    (h : ¬ ((e.support : Set ℕ) ⊆ Set.range (Fin.valEmbedding (n := M)))) :
    (e.prod fun m k => esymmFam M R m ^ k) = 0 := by
  classical
  rw [Set.not_subset] at h
  obtain ⟨m, hm, hnot⟩ := h
  have hmM : M ≤ m := by
    by_contra hlt
    exact hnot ⟨⟨m, Nat.not_le.mp hlt⟩, rfl⟩
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ (Finset.mem_coe.mp hm), esymmFam_eq_zero_of_le M R hmM,
    zero_pow (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hm)), zero_mul]

theorem coeff_subst_esymmFam (Q : MvPowerSeries ℕ R) (s : Fin M →₀ ℕ) (F : Finset (Fin M →₀ ℕ))
    (hF : ∀ f : Fin M →₀ ℕ, Finsupp.weight (fwt M) f = s.degree → f ∈ F) :
    coeff s (subst (esymmFam M R) Q)
      = MvPolynomial.coeff s (MvPolynomial.aeval (fun i : Fin M => MvPolynomial.esymm (Fin M) R (i.val + 1))
          (∑ f ∈ F, MvPolynomial.monomial f (coeff (ext M f) Q))) := by
  classical
  rw [coeff_subst (hasSubst_esymmFam M R)]
  have hsupp : Function.support (fun e : ℕ →₀ ℕ => coeff e Q • coeff s (e.prod fun m k => esymmFam M R m ^ k))
      ⊆ ((F.image (ext M) : Finset (ℕ →₀ ℕ)) : Set (ℕ →₀ ℕ)) := by
    intro e he
    rw [Function.mem_support] at he
    have hsub : (e.support : Set ℕ) ⊆ Set.range (Fin.valEmbedding (n := M)) := by
      by_contra hns
      exact he (by rw [prod_esymmFam_eq_zero_of_not_subset R M e hns, map_zero, smul_zero])
    have hw : Finsupp.weight awt e = s.degree := by
      by_contra hne
      exact he (by rw [coeff_prod_esymmFam_eq_zero M R e (fun h => hne h.symm), smul_zero])
    have hef : ext M (Finsupp.comapDomain Fin.valEmbedding e (Fin.valEmbedding.injective.injOn)) = e :=
      Finsupp.embDomain_comapDomain hsub
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨Finsupp.comapDomain Fin.valEmbedding e (Fin.valEmbedding.injective.injOn), ?_, hef⟩
    exact hF _ (by rw [← weight_ext M, hef, hw])
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun x _ y _ h => Finsupp.embDomain_injective _ h), map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul, prod_esymmFam_ext,
    prod_gFam_eq_coe, MvPolynomial.coeff_coe, smul_eq_mul]

theorem coeff_ext_eq_zero_of_coeff_subst_esymmFam_eq_zero (Q : MvPowerSeries ℕ R) (w : ℕ)
    (h : ∀ s : Fin M →₀ ℕ, s.degree = w → coeff s (subst (esymmFam M R) Q) = 0)
    (f : Fin M →₀ ℕ) (hf : Finsupp.weight (fwt M) f = w) : coeff (ext M f) Q = 0 := by
  classical
  set F : Finset (Fin M →₀ ℕ) :=
    ((Finset.range (w + 1)).biUnion fun dd => (Finset.univ : Finset (Fin M)).finsuppAntidiag dd).filter
      (fun f => Finsupp.weight (fwt M) f = w) with hFdef
  have hF : ∀ g : Fin M →₀ ℕ, Finsupp.weight (fwt M) g = w → g ∈ F := by
    intro g hg
    rw [hFdef, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ⟨g.degree, ?_, ?_⟩, hg⟩
    · rw [Finset.mem_range]
      have : g.degree ≤ Finsupp.weight (fwt M) g := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Finsupp.weight_apply]
        exact Finsupp.sum_le_sum fun i _ => by
          simp only [fwt, smul_eq_mul, mul_one]
          exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    · rw [Finset.mem_finsuppAntidiag]
      exact ⟨(Finsupp.degree_eq_sum g).symm, Finset.subset_univ _⟩
  set T : MvPolynomial (Fin M) R := ∑ g ∈ F, MvPolynomial.monomial g (coeff (ext M g) Q) with hT
  have hcoeffT : ∀ s : Fin M →₀ ℕ, MvPolynomial.coeff s
      (MvPolynomial.aeval (fun i : Fin M => MvPolynomial.esymm (Fin M) R (i.val + 1)) T) = 0 := by
    intro s
    by_cases hs : s.degree = w
    · rw [← coeff_subst_esymmFam R M Q s F (fun g hg => hF g (by rw [hg, hs]))]
      exact h s hs
    · have hhom : (MvPolynomial.aeval (fun i : Fin M => MvPolynomial.esymm (Fin M) R (i.val + 1)) T).IsHomogeneous w := by
        rw [hT, map_sum]
        apply MvPolynomial.IsHomogeneous.sum
        intro g hg
        have hgw : Finsupp.weight (fwt M) g = w := (Finset.mem_filter.mp hg).2
        rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, ← zero_add w, ← hgw]
        exact (MvPolynomial.isHomogeneous_C _ _).mul (isHomogeneous_prod_esymm M R g)
      exact hhom.coeff_eq_zero hs
  have hTeval : MvPolynomial.esymmAlgHom (Fin M) R M T = 0 := by
    apply Subtype.ext
    rw [MvPolynomial.esymmAlgHom_apply]
    ext s
    rw [hcoeffT]
    simp
  have hT0 : T = 0 := MvPolynomial.esymmAlgHom_fin_injective R le_rfl (by rw [hTeval, map_zero])
  have hread : MvPolynomial.coeff f T = coeff (ext M f) Q := by
    rw [hT, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq', if_pos (hF f hf)]
  rw [← hread, hT0, MvPolynomial.coeff_zero]

theorem upFam_self : upFam R M M = esymmFam M R := by
  funext m
  rw [upFam, esymmUpTo_top, esymmFam]

variable {d : ℕ} (Φ : MvFormalGroup d R)
variable (G : Fin d → MvPowerSeries ℕ R)
variable (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
variable (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))

include hG0 hG in

theorem coeff_eq_zero_of_coeff_subst_curveFam_eq_zero (K : ℕ)
    (hγ : ∀ (j : Fin d) (n : ℕ), n < K →
      PowerSeries.coeff n (MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j)) = 0)
    (j : Fin d) (e : ℕ →₀ ℕ) (he : Finsupp.weight awt e < K) : coeff e (G j) = 0 := by
  classical

  have hsub : (e.support : Set ℕ) ⊆ Set.range (Fin.valEmbedding (n := K)) := by
    intro m hm
    have hm' : e m ≠ 0 := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hm)
    have hle : awt m ≤ Finsupp.weight awt e := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      calc awt m ≤ e m • awt m := by
            rw [smul_eq_mul]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm')
        _ ≤ ∑ i ∈ e.support, e i • awt i :=
            Finset.single_le_sum (f := fun i => e i • awt i) (fun _ _ => Nat.zero_le _) (Finset.mem_coe.mp hm)
    exact ⟨⟨m, by simp only [awt] at hle; omega⟩, rfl⟩
  have hef : ext K (Finsupp.comapDomain Fin.valEmbedding e (Fin.valEmbedding.injective.injOn)) = e :=
    Finsupp.embDomain_comapDomain hsub
  rw [← hef]
  refine coeff_ext_eq_zero_of_coeff_subst_esymmFam_eq_zero R K (G j) _ ?_ _ rfl
  intro s hs
  have hsK : s.degree < K := by
    rw [hs, ← weight_ext K, hef]
    exact he
  rw [← upFam_self R K]
  exact coeff_subst_upFam_eq_zero R K Φ G hG0 hG K hγ K le_rfl j s hsK

end Final

section Omega

omit N in

theorem coeff_subst_eq_zero_of_order {σ τ : Type*} [Finite σ] (b : σ → MvPowerSeries τ R)
    (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries σ R) (K : ℕ)
    (hf : ∀ e : σ →₀ ℕ, e.degree < K → coeff e f = 0) (n : τ →₀ ℕ) (hn : n.degree < K) :
    coeff n (subst b f) = 0 := by
  classical
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hb)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < K
  · rw [hf e he, zero_smul]
  · rw [MvFormalGroup.coeff_finsuppProd_pow_eq_zero_of_degree_lt hb (by omega), smul_zero]

omit N in
theorem negX_pow_eq (m : ℕ) :
    (-PowerSeries.X : PowerSeries R) ^ m = MvPowerSeries.C ((-1 : R) ^ m) * (MvPowerSeries.X () : PowerSeries R) ^ m := by
  rw [neg_pow, map_pow, map_neg, map_one]
  rfl

omit N in
theorem coeff_negX_pow (m : ℕ) (n : Unit →₀ ℕ) :
    coeff n ((-PowerSeries.X : PowerSeries R) ^ m) = if n = Finsupp.single () m then (-1 : R) ^ m else 0 := by
  classical
  rw [negX_pow_eq, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

def omegaPair : Fin 2 × ℕ → PowerSeries R :=
  fun ik => if ik.1 = 0 then (-PowerSeries.X : PowerSeries R) ^ (ik.2 + 1)
    else MvFormalGroup.CartierModule.curveFam R ik.2

omit N in
theorem omegaPair_zero (m : ℕ) : omegaPair R (0, m) = (-PowerSeries.X : PowerSeries R) ^ (m + 1) := if_pos rfl
omit N in
theorem omegaPair_one (m : ℕ) : omegaPair R (1, m) = MvFormalGroup.CartierModule.curveFam R m :=
  if_neg (fun h => (one_ne_zero : (1 : Fin 2) ≠ 0) h)

omit N in
theorem hasSubst_omegaPair : HasSubst (omegaPair R) := by
  classical
  refine ⟨fun ik => ?_, fun s => ?_⟩
  · rcases ik with ⟨i, k⟩
    by_cases hi : i = 0
    · subst hi
      rw [omegaPair_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_negX_pow, if_neg]
      · exact IsNilpotent.zero
      · intro h
        have := congrArg Finsupp.degree h
        rw [map_zero, Finsupp.degree_single] at this
        omega
    · rw [show i = 1 by omega, omegaPair_one, MvFormalGroup.CartierModule.constantCoeff_curveFam]
      exact IsNilpotent.zero
  · refine (((Finset.univ : Finset (Fin 2)) ×ˢ Finset.range (s.degree + 1)).finite_toSet).subset fun ik hik => ?_
    rcases ik with ⟨i, k⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and, Finset.mem_range]
    by_contra hk
    apply hik
    by_cases hi : i = 0
    · subst hi
      rw [omegaPair_zero, coeff_negX_pow, if_neg]
      intro h
      have := congrArg Finsupp.degree h
      rw [Finsupp.degree_single] at this
      omega
    · rw [show i = 1 by omega, omegaPair_one]
      cases k with
      | zero => omega
      | succ k => exact map_zero _

omit N in

theorem subst_omegaPair_addFam (m : ℕ) : subst (omegaPair R) (MvFormalGroup.BigWittLaw.addFam R m) = 0 := by
  classical
  have hθ := hasSubst_omegaPair R
  rw [MvFormalGroup.BigWittLaw.addFam_eq, ← coe_substAlgHom hθ, map_add, map_add, map_sum]
  simp only [map_mul, coe_substAlgHom, subst_X hθ, omegaPair_zero, omegaPair_one]
  cases m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, add_zero, pow_one]
    show -PowerSeries.X + PowerSeries.X = (0 : PowerSeries R)
    ring
  | succ m' =>
    rw [Finset.sum_eq_single_of_mem m' (Finset.mem_range.mpr (Nat.lt_succ_self m'))]
    · have h0 : m' + 1 - 1 - m' = 0 := by omega
      rw [h0]
      show (-PowerSeries.X) ^ (m' + 1 + 1) + (0 : PowerSeries R) + (-PowerSeries.X) ^ (m' + 1) * PowerSeries.X = 0
      ring
    · intro i hi hne
      have : m' + 1 - 1 - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk]
      show (-PowerSeries.X) ^ (i + 1) * (0 : PowerSeries R) = 0
      rw [mul_zero]

variable {d : ℕ} (Φ : MvFormalGroup d R)
variable (G : Fin d → MvPowerSeries ℕ R)
variable (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
variable (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))

include hG0 hG in

theorem subst_curveFam_eq_negSeries :
    (fun j => subst (MvFormalGroup.CartierModule.curveFam R) (G j))
      = MvFormalGroup.negSeries Φ fun j => subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j) := by
  classical
  have hθ := hasSubst_omegaPair R
  have hB0 : HasSubst (fun m : ℕ => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    HasSubst.X_comp (Prod.mk 0)
  have hB1 : HasSubst (fun m : ℕ => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    HasSubst.X_comp (Prod.mk 1)
  have hE : HasSubst (Sum.elim
        (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (l | l)
    · exact constantCoeff_subst_eq_zero hB0 (fun m => constantCoeff_X _) (hG0 l)
    · exact constantCoeff_subst_eq_zero hB1 (fun m => constantCoeff_X _) (hG0 l)
  have hu0 : ∀ j, constantCoeff (subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0 := by
    intro j
    refine constantCoeff_subst_eq_zero ?_ (fun m => ?_) (hG0 j)
    · have : (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) = fun m => omegaPair R (0, m) :=
        funext fun m => (omegaPair_zero R m).symm
      rw [this]
      exact ⟨fun m => hθ.const_coeff (0, m), fun s => (hθ.coeff_zero s).preimage fun _ _ _ _ h => by simpa using h⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_negX_pow, if_neg]
      intro h; have := congrArg Finsupp.degree h; rw [map_zero, Finsupp.degree_single] at this; omega
  apply MvFormalGroup.negSeries_unique Φ hu0 (fun j => constantCoeff_subst_eq_zero
    (MvFormalGroup.CartierModule.hasSubst_curveFam (R := R)) (MvFormalGroup.CartierModule.constantCoeff_curveFam (R := R)) (hG0 j))
  intro j
  have key : subst (omegaPair R) (subst (MvFormalGroup.BigWittLaw.addFam R) (G j)) = 0 := by
    rw [subst_comp_subst_apply (MvFormalGroup.BigWittLaw.hasSubst_addFam R) hθ]
    have h0 : (fun m => subst (omegaPair R) (MvFormalGroup.BigWittLaw.addFam R m)) = fun _ => 0 :=
      funext (subst_omegaPair_addFam R)
    rw [h0]
    refine MvPowerSeries.ext fun n => ?_
    rw [map_zero]
    exact coeff_subst_eq_zero_of_lt R _ HasSubst.zero (n.degree + 1) (fun _ _ _ => by rw [map_zero]) (G j)
      (hG0 j) n (Nat.lt_succ_self _)
  rw [hG j, subst_comp_subst_apply hE hθ] at key
  have hfam : (fun x => subst (omegaPair R) (Sum.elim
        (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l)) x))
      = Sum.elim (fun j => subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j))
          (fun j => subst (MvFormalGroup.CartierModule.curveFam R) (G j)) := by
    funext x
    rcases x with l | l
    · show subst (omegaPair R) (subst _ (G l)) = subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G l)
      rw [subst_comp_subst_apply hB0 hθ]
      congr 1
      funext m
      rw [subst_X hθ, omegaPair_zero]
    · show subst (omegaPair R) (subst _ (G l)) = subst (MvFormalGroup.CartierModule.curveFam R) (G l)
      rw [subst_comp_subst_apply hB1 hθ]
      congr 1
      funext m
      rw [subst_X hθ, omegaPair_one]
  rw [hfam] at key
  exact key

include hG0 hG in

theorem coeff_eq_zero_of_coeff_subst_pow_eq_zero (K : ℕ)
    (h : ∀ (j : Fin d) (n : ℕ), n < K →
      PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0)
    (j : Fin d) (e : ℕ →₀ ℕ) (he : Finsupp.weight (fun m : ℕ => m + 1) e < K) :
    MvPowerSeries.coeff e (G j) = 0 := by
  classical
  refine coeff_eq_zero_of_coeff_subst_curveFam_eq_zero R Φ G hG0 hG K ?_ j e he

  intro j' n hn
  have hω : HasSubst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) := by
    refine ⟨fun m => ?_, fun s => ?_⟩
    · rw [map_pow, show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, constantCoeff_X,
        zero_pow (Nat.succ_ne_zero m)]
      exact IsNilpotent.zero
    · refine (Set.finite_singleton (s.degree - 1)).subset fun m hm => ?_
      by_contra hne
      apply hm
      rw [show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, coeff_X_pow, if_neg]
      intro hs
      apply hne
      rw [hs, Finsupp.degree_single]
      rfl

  set u : Fin d → PowerSeries R := fun j => subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j) with hu
  have hneg : HasSubst (fun _ : Unit => (-PowerSeries.X : PowerSeries R)) :=
    hasSubst_of_constantCoeff_zero fun _ => by
      rw [map_neg, show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, constantCoeff_X, neg_zero]
  have hu_eq : ∀ j, subst (fun _ : Unit => (-PowerSeries.X : PowerSeries R))
      (subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = u j := by
    intro j
    rw [subst_comp_subst_apply hω hneg]
    show subst (fun m => subst (fun _ : Unit => (-PowerSeries.X : PowerSeries R))
        ((MvPowerSeries.X () : PowerSeries R) ^ (m + 1))) (G j)
      = subst (fun m => (-PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)
    congr 1
    funext m
    rw [subst_pow hneg, subst_X hneg]
  have hu_van : ∀ (j : Fin d) (s : Unit →₀ ℕ), s.degree < K → coeff s (u j) = 0 := by
    intro j s hs
    rw [← hu_eq]
    refine coeff_subst_eq_zero_of_order R _ (fun _ => by
      rw [map_neg, show (PowerSeries.X : PowerSeries R) = MvPowerSeries.X () from rfl, constantCoeff_X, neg_zero])
      _ K (fun e' he' => ?_) s hs
    have he'eq : e' = Finsupp.single () (e' ()) := by ext u; simp
    rw [he'eq]
    have := h j (e' ()) (by rw [he'eq, Finsupp.degree_single] at he'; exact he')
    exact this
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hu_van j 0 (by rw [map_zero]; omega)

  have hcurve := subst_curveFam_eq_negSeries R Φ G hG0 hG
  have hinv : MvFormalGroup.negSeries Φ u = fun i => subst u (MvFormalGroup.invSeries Φ i) := by
    have hX0 : ∀ j : Fin d, ((MvPowerSeries.X j : MvPowerSeries (Fin d) R)).constantCoeff = 0 :=
      fun j => constantCoeff_X _
    have := MvFormalGroup.subst_negSeries Φ (a := fun j : Fin d => (MvPowerSeries.X j : MvPowerSeries (Fin d) R))
      hX0 (b := u) hu0
    rw [MvFormalGroup.invSeries]
    rw [this]
    congr 1
    funext i
    rw [subst_X (hasSubst_of_constantCoeff_zero hu0)]
  have hval : subst (MvFormalGroup.CartierModule.curveFam R) (G j') = subst u (MvFormalGroup.invSeries Φ j') := by
    have := congrFun hcurve j'
    rw [this, hinv]
  have hs : (Finsupp.single () n : Unit →₀ ℕ).degree < K := by rw [Finsupp.degree_single]; exact hn
  have := coeff_subst_eq_zero_of_lt R u (hasSubst_of_constantCoeff_zero hu0) K hu_van
    (MvFormalGroup.invSeries Φ j') (MvFormalGroup.constantCoeff_invSeries Φ j') (Finsupp.single () n) hs
  rw [hval]
  exact this

end Omega

end MvFormalGroup.BigWittLaw.K0q

end

theorem solution
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R)
    (G : Fin d → MvPowerSeries ℕ R)
    (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    (K : ℕ)
    (h : ∀ (j : Fin d) (n : ℕ), n < K →
      PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0)
    (j : Fin d) (e : ℕ →₀ ℕ) (he : Finsupp.weight (fun m : ℕ => m + 1) e < K) :
    MvPowerSeries.coeff e (G j) = 0 :=
  MvFormalGroup.BigWittLaw.K0q.coeff_eq_zero_of_coeff_subst_pow_eq_zero R Φ G hG0 hG K h j e he

end S_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero (solution)
