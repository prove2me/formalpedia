-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_forall_coeff_sub_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/45f09e2a-b1b5-55e7-a8cb-32fa5852f091

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero

set_option autoImplicit false

universe u

open MvPowerSeries

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

theorem complete
    (t : ℕ → CartierModule p Φ) (N : ℕ → ℕ) (hN : Monotone N)
    (hN' : ∀ B : ℕ, ∃ K, B ≤ N K)
    (ht : ∀ (k : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N k → coeff e ((t k).toPowerSeries j) = 0) :
    ∃ s : CartierModule p Φ, ∀ (K : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N K →
        coeff e ((s - ∑ k ∈ Finset.range K, t k).toPowerSeries j) = 0 := by
  classical

  set S : ℕ → CartierModule p Φ := fun K => ∑ k ∈ Finset.range K, t k with hS
  have hSsucc : ∀ K, S (K + 1) = S K + t K := fun K => by
    simp only [hS, Finset.sum_range_succ]

  have hSS : ∀ K K', K ≤ K' → Cong (N K) (S K') (S K) := by
    intro K K' hKK'
    induction K', hKK' using Nat.le_induction with
    | base => exact Cong.refl _ _
    | succ K' hKK' ih =>
      rw [hSsucc]
      refine Cong.trans ?_ ih
      exact Cong.add_small (S K') fun l => (fun e he => ht K' l e (lt_of_lt_of_le he (hN hKK')))

  let K₀ : (ℕ →₀ ℕ) → ℕ := fun e => Nat.find (hN' (Finsupp.weight (fun m : ℕ => p ^ m) e + 1))
  have hK₀ : ∀ e, Finsupp.weight (fun m : ℕ => p ^ m) e < N (K₀ e) := fun e =>
    Nat.find_spec (hN' (Finsupp.weight (fun m : ℕ => p ^ m) e + 1))
  let s₀ : Fin d → MvPowerSeries ℕ R := fun j e => coeff e ((S (K₀ e)).toPowerSeries j)
  have hs₀ : ∀ (K : ℕ) (j : Fin d), WV (wN p) (N K) (s₀ j - (S K).toPowerSeries j) := by
    intro K j e he
    rw [map_sub, sub_eq_zero]
    show coeff e ((S (K₀ e)).toPowerSeries j) = coeff e ((S K).toPowerSeries j)
    have h1 := hSS K (max K (K₀ e)) (le_max_left _ _) j e he
    have h2 := hSS (K₀ e) (max K (K₀ e)) (le_max_right _ _) j e (hK₀ e)
    rw [map_sub, sub_eq_zero] at h1 h2
    rw [← h1, ← h2]

  let s : CartierModule p Φ :=
    { toPowerSeries := s₀
      constantCoeff_eq_zero := fun j => by
        show coeff 0 ((S (K₀ 0)).toPowerSeries j) = 0
        rw [coeff_zero_eq_constantCoeff_apply]
        exact (S (K₀ 0)).constantCoeff_eq_zero j
      subst_eq := by
        intro j
        ext E
        obtain ⟨K, hK⟩ := hN' (Finsupp.weight (weight p fun _ : Fin 2 => 1) E + 1)
        have hs₀c : ∀ l, (s₀ l).constantCoeff = 0 := fun l => by
          show coeff 0 ((S (K₀ 0)).toPowerSeries l) = 0
          rw [coeff_zero_eq_constantCoeff_apply]
          exact (S (K₀ 0)).constantCoeff_eq_zero l

        have hL : WV (weight p fun _ : Fin 2 => 1) (N K)
            (subst (addFam p R) (s₀ j) - subst (addFam p R) ((S K).toPowerSeries j)) := by
          rw [← coe_substAlgHom (hasSubst_addFam p R), ← map_sub, coe_substAlgHom]
          exact WV.subst_of_raise (hasSubst_addFam p R) (WV_addFam (p := p) (R := R)) (hs₀ K j)

        have hblk : ∀ (i : Fin 2) (x y : Fin d → MvPowerSeries ℕ R) (l : Fin d),
            WV (wN p) (N K) (x l - y l) →
            WV (weight p fun _ : Fin 2 => 1) (N K)
              (subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (x l) -
                subst (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) (y l)) := by
          intro i x y l hxy
          change WV (weight p fun _ : Fin 2 => 1) (N K) (subst (blk i) (x l) - subst (blk i) (y l))
          rw [← coe_substAlgHom (hasSubst_blk i), ← map_sub, coe_substAlgHom]
          exact WV.subst_of_raise (hasSubst_blk i) (WV_blk (p := p) (R := R) i) hxy
        have hE1 : HasSubst (Sum.elim
            (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s₀ l))
            fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (s₀ l)) := by
          apply hasSubst_of_constantCoeff_zero
          rintro (l | l)
          · exact constantCoeff_inBlk 0 hs₀c l
          · exact constantCoeff_inBlk 1 hs₀c l
        have hE2 : HasSubst (Sum.elim
            (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) ((S K).toPowerSeries l))
            fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) ((S K).toPowerSeries l)) := by
          apply hasSubst_of_constantCoeff_zero
          rintro (l | l)
          · exact constantCoeff_inBlk 0 (S K).constantCoeff_eq_zero l
          · exact constantCoeff_inBlk 1 (S K).constantCoeff_eq_zero l
        have hR := WV.subst_sub hE1 hE2 (N := N K) (by
          rintro (l | l)
          · exact hblk 0 _ _ l (hs₀ K l)
          · exact hblk 1 _ _ l (hs₀ K l)) (Φ.toPowerSeries j)
        have hSK := (S K).subst_eq j
        have key := (hL.sub hR) E (by omega)
        rw [map_sub, map_sub, map_sub, hSK, sub_sub_sub_cancel_right, sub_eq_zero] at key
        exact key }
  refine ⟨s, fun K j e he => ?_⟩
  have h1 : Cong (N K) s (S K) := fun l => hs₀ K l
  have h2 := (h1.sub_left (S K)) j e he
  rw [sub_self, map_sub, sub_eq_zero] at h2
  rw [h2]
  show coeff e (0 : MvPowerSeries ℕ R) = 0
  rw [map_zero]

end K4

end B23K4

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (t : ℕ → MvFormalGroup.CartierModule p Φ) (N : ℕ → ℕ) (hN : Monotone N)
    (hN' : ∀ B : ℕ, ∃ K, B ≤ N K)
    (ht : ∀ (k : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N k → MvPowerSeries.coeff e ((t k).toPowerSeries j) = 0) :
    ∃ s : MvFormalGroup.CartierModule p Φ, ∀ (K : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N K →
        MvPowerSeries.coeff e ((s - ∑ k ∈ Finset.range K, t k).toPowerSeries j) = 0 :=
  B23K4.complete t N hN hN' ht

end S_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero (solution)
