-- Prove2me | solution 1 for MvFormalGroup.exists_rescaledLog_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/85ba7b0c-87c1-5b82-9082-8c20eb30cfb8

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
import Theorems.Thm_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete

set_option autoImplicit false

namespace S17LE

open MvPowerSeries

section Cong

variable {S : Type*} [CommRing S] {σ : Type*}

def Cong (n : ℕ) (f g : MvPowerSeries σ S) : Prop := ∀ m : σ →₀ ℕ, m.degree ≤ n → coeff m f = coeff m g

namespace Cong

variable {n : ℕ} {f g h : MvPowerSeries σ S}

theorem refl (f : MvPowerSeries σ S) : Cong n f f := fun _ _ => rfl
theorem symm (hfg : Cong n f g) : Cong n g f := fun m hm => (hfg m hm).symm
theorem trans (hfg : Cong n f g) (hgh : Cong n g h) : Cong n f h := fun m hm => (hfg m hm).trans (hgh m hm)
theorem of_eq (e : f = g) : Cong n f g := fun _ _ => by rw [e]
theorem mono {n' : ℕ} (h' : n' ≤ n) (hfg : Cong n f g) : Cong n' f g := fun m hm => hfg m (hm.trans h')

theorem add {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f + f') (g + g') :=
  fun m hm => by rw [map_add, map_add, h₁ m hm, h₂ m hm]
theorem neg (h₁ : Cong n f g) : Cong n (-f) (-g) := fun m hm => by rw [map_neg, map_neg, h₁ m hm]
theorem sub {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f - f') (g - g') :=
  fun m hm => by rw [map_sub, map_sub, h₁ m hm, h₂ m hm]
theorem smul (c : S) (h₁ : Cong n f g) : Cong n (c • f) (c • g) :=
  fun m hm => by rw [map_smul, map_smul, h₁ m hm]

theorem sum {ι : Type*} (s : Finset ι) {F G : ι → MvPowerSeries σ S} (h : ∀ i ∈ s, Cong n (F i) (G i)) :
    Cong n (∑ i ∈ s, F i) (∑ i ∈ s, G i) := fun m hm => by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi m hm

theorem mul {f' g' : MvPowerSeries σ S} (h₁ : Cong n f g) (h₂ : Cong n f' g') : Cong n (f * f') (g * g') := by
  classical
  intro m hm
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h1 : x.1.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  have h2 : x.2.degree ≤ n := by
    have := congrArg Finsupp.degree hx'; rw [map_add] at this; omega
  rw [h₁ _ h1, h₂ _ h2]

theorem prod {ι : Type*} (s : Finset ι) {F G : ι → MvPowerSeries σ S} (h : ∀ i ∈ s, Cong n (F i) (G i)) :
    Cong n (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pow (h₁ : Cong n f g) (k : ℕ) : Cong n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero]; exact refl _
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h₁

theorem finsuppProd {ι : Type*} (d : ι →₀ ℕ) {F G : ι → MvPowerSeries σ S} (h : ∀ i, Cong n (F i) (G i)) :
    Cong n (d.prod fun i e => F i ^ e) (d.prod fun i e => G i ^ e) :=
  prod _ fun i _ => (h i).pow _

theorem iff_le_order : Cong n f g ↔ ((n + 1 : ℕ) : ℕ∞) ≤ (f - g).order := by
  constructor
  · intro h
    exact nat_le_order fun m hm => by rw [map_sub, h m (by omega), sub_self]
  · intro h m hm
    have := coeff_of_lt_order (d := m) (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) h)
    rwa [map_sub, sub_eq_zero] at this

theorem zero_iff_le_order : Cong n f 0 ↔ ((n + 1 : ℕ) : ℕ∞) ≤ f.order := by
  rw [iff_le_order, sub_zero]

theorem substLeft {τ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hfg : Cong n f g) : Cong n (subst a f) (subst a g) := by
  rw [iff_le_order] at hfg ⊢
  rw [← subst_sub ha]
  refine hfg.trans ((le_mul_of_one_le_left (by simp) ?_).trans (le_order_subst ha _))
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, ha0]

theorem substRight {τ : Type*} {a b : τ → MvPowerSeries σ S} (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, Cong n (a i) (b i)) (F : MvPowerSeries τ S) : Cong n (subst a F) (subst b F) := by
  intro m hm
  rw [coeff_subst ha, coeff_subst hb]
  exact finsum_congr fun d => by rw [(finsuppProd d hab) m hm]

end Cong

theorem card_le_order_prod {ι : Type*} (s : Finset ι) (u : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) : (s.card : ℕ∞) ≤ (∏ i ∈ s, u i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, add_comm]
    refine le_trans (add_le_add ?_ (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))) le_order_mul
    refine nat_le_order fun d hd => ?_
    have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hu a (Finset.mem_insert_self a s)]

theorem Cong.prod_of_cong_one {ι : Type*} (s : Finset ι) (u v : ι → MvPowerSeries σ S)
    (hu : ∀ i ∈ s, constantCoeff (u i) = 0) (hv : ∀ i ∈ s, constantCoeff (v i) = 0)
    (h : ∀ i ∈ s, Cong 1 (u i) (v i)) : Cong s.card (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Cong.refl _
  | insert a s ha ih =>
    have hu' := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hv' := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have ih' := ih hu' hv' fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Cong.iff_le_order,
      show u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        (u a - v a) * ∏ i ∈ s, u i + v a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) by ring]
    refine le_trans ?_ min_order_le_add
    refine le_min ?_ ?_
    ·
      have h1 : ((2 : ℕ) : ℕ∞) ≤ (u a - v a).order := by
        have := (Cong.iff_le_order).1 (h a (Finset.mem_insert_self a s)); exact_mod_cast this
      have h2 := card_le_order_prod s u hu'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (2 : ℕ) + (s.card : ℕ∞) := by push_cast; ring
        _ ≤ (u a - v a).order + (∏ i ∈ s, u i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul
    ·
      have h1 : ((1 : ℕ) : ℕ∞) ≤ (v a).order := nat_le_order fun d hd => by
        have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
        rw [this, coeff_zero_eq_constantCoeff_apply, hv a (Finset.mem_insert_self a s)]
      have h2 : ((s.card + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ s, u i - ∏ i ∈ s, v i).order := (Cong.iff_le_order).1 ih'
      calc ((s.card + 1 + 1 : ℕ) : ℕ∞) = (1 : ℕ) + ((s.card + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (v a).order + (∏ i ∈ s, u i - ∏ i ∈ s, v i).order := add_le_add h1 h2
        _ ≤ _ := le_order_mul

theorem finsuppProd_eq_prod_sigma {ι : Type*} (d : ι →₀ ℕ) (F : ι → MvPowerSeries σ S) :
    (d.prod fun i e => F i ^ e) = ∏ x ∈ d.support.sigma (fun i => Finset.range (d i)), F x.1 := by
  rw [Finsupp.prod, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Finset.prod_const, Finset.card_range]

theorem card_sigma_range {ι : Type*} (d : ι →₀ ℕ) : (d.support.sigma fun i => Finset.range (d i)).card = d.degree := by
  rw [Finset.card_sigma, Finsupp.degree_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.card_range _

theorem Cong.aeval_of_isHomogeneous {τ : Type*} {N : ℕ} (P : MvPolynomial τ S) (hP : P.IsHomogeneous N)
    (a b : τ → MvPowerSeries σ S) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, Cong 1 (a i) (b i)) :
    Cong N (MvPolynomial.aeval a P : MvPowerSeries σ S) (MvPolynomial.aeval b P) := by
  classical
  have key : ∀ d ∈ P.support, Cong N (d.prod fun i e => a i ^ e) (d.prod fun i e => b i ^ e) := by
    intro d hd
    have hdeg : d.degree = N := by
      have := hP (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.degree_eq_weight_one]
      simpa [Pi.one_def] using this
    rw [finsuppProd_eq_prod_sigma, finsuppProd_eq_prod_sigma, ← hdeg, ← card_sigma_range d]
    exact Cong.prod_of_cong_one _ _ _ (fun x _ => ha x.1) (fun x _ => hb x.1) (fun x _ => hab x.1)
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  refine Cong.sum _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  exact (Cong.refl _).mul (key d hd)

end Cong

section Pieces

variable {S : Type*} [CommRing S] {σ : Type*}

section Fin
variable [Fintype σ]

open Classical in

noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f => Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

private noncomputable def _root_.S17LE.homogPart (N : ℕ) (g : MvPowerSeries σ S) : MvPolynomial σ S :=
  ∑ m ∈ (lowDeg σ N).filter (fun m => m.degree = N), MvPolynomial.monomial m (coeff m g)

p2m_export "S17LE" "homogPart"
theorem coeff_homogPart (N : ℕ) (g : MvPowerSeries σ S) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (homogPart N g) = if m.degree = N then coeff m g else 0 := by
  classical
  rw [homogPart, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_lowDeg]
  by_cases h : m.degree = N
  · rw [if_pos ⟨h.le, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

theorem isHomogeneous_homogPart (N : ℕ) (g : MvPowerSeries σ S) : (homogPart N g).IsHomogeneous N := by
  classical
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  exact MvPolynomial.isHomogeneous_monomial _ (Finset.mem_filter.1 hm).2

theorem Cong.homogPart {N : ℕ} {g : MvPowerSeries σ S} (hg : Cong N g 0) :
    Cong (N + 1) g (homogPart (N + 1) g : MvPolynomial σ S) := by
  intro m hm
  rw [MvPolynomial.coeff_coe, coeff_homogPart]
  split_ifs with h
  · rfl
  · rw [hg m (by omega), map_zero]

omit [Fintype σ] in

theorem eq_of_cong_of_isHomogeneous {N : ℕ} {P Q : MvPolynomial σ S} (hP : P.IsHomogeneous N) (hQ : Q.IsHomogeneous N)
    (h : Cong N (P : MvPowerSeries σ S) Q) : P = Q := by
  ext m
  by_cases hm : m.degree ≤ N
  · have := h m hm
    rwa [MvPolynomial.coeff_coe, MvPolynomial.coeff_coe] at this
  · rw [hP.coeff_eq_zero (by omega), hQ.coeff_eq_zero (by omega)]

end Fin

theorem exists_eq_single_of_degree_eq_one {m : σ →₀ ℕ} (hm : m.degree = 1) : ∃ u, m = Finsupp.single u 1 := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.2 hm0
  have hu1 : m u = 1 := by
    have h1 := Finsupp.le_degree u m
    have h2 := Finsupp.mem_support_iff.1 hu
    omega
  refine ⟨u, ?_⟩
  have hle : Finsupp.single u 1 ≤ m := Finsupp.single_le_iff.2 hu1.ge
  have hrest : m - Finsupp.single u 1 = 0 := by
    apply (Finsupp.degree_eq_zero_iff _).1
    have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
    rw [map_add, Finsupp.degree_single, hm] at this
    omega
  have := tsub_add_cancel_of_le hle
  rw [hrest, zero_add] at this
  exact this.symm

theorem Cong.one_iff {f g : MvPowerSeries σ S} :
    Cong 1 f g ↔ constantCoeff f = constantCoeff g ∧ ∀ u, coeff (Finsupp.single u 1) f = coeff (Finsupp.single u 1) g := by
  constructor
  · intro h
    exact ⟨by rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]; exact h 0 (by simp),
      fun u => h _ (by rw [Finsupp.degree_single])⟩
  · rintro ⟨h0, h1⟩ m hm
    rcases Nat.lt_or_ge m.degree 1 with hlt | hge
    · have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    · obtain ⟨u, rfl⟩ := exists_eq_single_of_degree_eq_one (m := m) (by omega)
      exact h1 u

theorem coeff_mapDomain_subst_X_comp {τ : Type*} {e : σ → τ} (he : Function.Injective e) (g : MvPowerSeries σ S)
    (d : σ →₀ ℕ) : coeff (d.mapDomain e) (subst (fun s => (X (e s) : MvPowerSeries τ S)) g) = coeff d g := by
  classical
  have ha : HasSubst (fun s => (X (e s) : MvPowerSeries τ S)) := by
    refine ⟨fun s => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d' => ?_⟩
    apply Set.Subsingleton.finite
    intro s₁ h₁ s₂ h₂
    simp only [Set.mem_setOf_eq, coeff_X] at h₁ h₂
    split_ifs at h₁ h₂ with e₁ e₂
    · rw [e₁] at e₂; exact he (Finsupp.single_left_injective one_ne_zero e₂)
    all_goals simp_all
  have hmono : ∀ d' : σ →₀ ℕ, (d'.prod fun s k => (X (e s) : MvPowerSeries τ S) ^ k) = monomial (d'.mapDomain e) 1 := by
    intro d'
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_mapDomain_index_inj he]
  rw [coeff_subst ha, finsum_eq_single _ d]
  · rw [hmono, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d' hd'
    rw [hmono, coeff_monomial, if_neg (fun h => hd' (Finsupp.mapDomain_injective he h).symm), smul_zero]

end Pieces

section Lazard

variable {K : Type*} [CommRing K] {d : ℕ} (F : MvFormalGroup d K)

noncomputable def inlX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j => X (Sum.inl j)
noncomputable def inrX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j => X (Sum.inr j)

omit F in
theorem constantCoeff_inlX (j : Fin d) : constantCoeff (inlX (K := K) j) = 0 := constantCoeff_X _
omit F in
theorem constantCoeff_inrX (j : Fin d) : constantCoeff (inrX (K := K) j) = 0 := constantCoeff_X _

noncomputable def Edef (φ : Fin d → MvPowerSeries (Fin d) K) (i : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) K :=
  subst F.toPowerSeries (φ i) - subst inlX (φ i) - subst inrX (φ i)

theorem cong_one_law (i : Fin d) : Cong 1 (F.toPowerSeries i) (inlX i + inrX i) := by
  classical
  rw [Cong.one_iff]
  refine ⟨by rw [F.constantCoeff_eq_zero, map_add, constantCoeff_inlX, constantCoeff_inrX, add_zero], ?_⟩
  rintro (j | j)
  · rw [F.coeff_single_inl, map_add, inlX, inrX, coeff_X, coeff_X]
    by_cases h : i = j
    · subst h; simp [Finsupp.single_eq_single_iff]
    · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]
  · rw [F.coeff_single_inr, map_add, inlX, inrX, coeff_X, coeff_X]
    by_cases h : i = j
    · subst h; simp [Finsupp.single_eq_single_iff]
    · simp [Finsupp.single_eq_single_iff, h, Ne.symm h]

theorem subst_Edef {τ : Type*} (φ : Fin d → MvPowerSeries (Fin d) K) (hφ : ∀ i, constantCoeff (φ i) = 0)
    {a b : Fin d → MvPowerSeries τ K} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (i : Fin d) :
    subst (Sum.elim a b) (Edef F φ i) =
      subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ i) - subst a (φ i) - subst b (φ i) := by
  have hab := MvFormalGroup.hasSubst_elim ha hb
  rw [Edef, subst_sub hab, subst_sub hab, subst_comp_subst_apply F.hasSubst_toPowerSeries hab,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero constantCoeff_inlX) hab,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero constantCoeff_inrX) hab]
  congr 2
  · congr 1; funext j; rw [inlX, subst_X hab]; rfl
  · congr 1; funext j; rw [inrX, subst_X hab]; rfl

structure Stage (n : ℕ) where
  φ : Fin d → MvPowerSeries (Fin d) K
  const : ∀ i, constantCoeff (φ i) = 0
  lin : ∀ i, Cong 1 (φ i) (X i)
  addit : ∀ i, Cong n (Edef F φ i) 0

noncomputable def stageOne : Stage F 1 where
  φ := fun i => X i
  const := fun i => constantCoeff_X i
  lin := fun _ => Cong.refl _
  addit := fun i => by
    have h : Edef F (fun i => X i) i = F.toPowerSeries i - (inlX i + inrX i) := by
      rw [Edef, subst_X F.hasSubst_toPowerSeries, subst_X (hasSubst_of_constantCoeff_zero constantCoeff_inlX),
        subst_X (hasSubst_of_constantCoeff_zero constantCoeff_inrX)]
      ring
    rw [h]
    have := (cong_one_law F i).sub (Cong.refl (inlX i + inrX i))
    rwa [sub_self] at this

variable [F.IsComm]

section Step

variable {F} {n : ℕ} (s : Stage F (n + 1))

noncomputable def Γ (i : Fin d) : MvPolynomial (Fin d ⊕ Fin d) K := homogPart (n + 2) (Edef F s.φ i)

omit [F.IsComm] in
theorem cong_E_Γ (i : Fin d) : Cong (n + 2) (Edef F s.φ i) (Γ s i : MvPolynomial (Fin d ⊕ Fin d) K) :=
  (s.addit i).homogPart

omit [F.IsComm] in
theorem isHomogeneous_Γ (i : Fin d) : (Γ s i).IsHomogeneous (n + 2) := isHomogeneous_homogPart _ _

theorem subst_swap_E (i : Fin d) :
    subst (fun u => (X (Sum.swap u) : MvPowerSeries (Fin d ⊕ Fin d) K)) (Edef F s.φ i) = Edef F s.φ i := by
  have hsw : (fun u => (X (Sum.swap u) : MvPowerSeries (Fin d ⊕ Fin d) K)) = Sum.elim inrX inlX := by
    funext u; rcases u with j | j <;> rfl
  rw [hsw, subst_Edef F s.φ s.const constantCoeff_inrX constantCoeff_inlX, Edef]
  have hcomm : (fun j => subst (Sum.elim inrX inlX) (F.toPowerSeries j)) = F.toPowerSeries := by
    funext j; exact MvFormalGroup.IsComm.comm (F := F) j
  rw [hcomm]
  ring

theorem rename_swap_Γ (i : Fin d) : MvPolynomial.rename Sum.swap (Γ s i) = Γ s i := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain Sum.swap (Finsupp.mapDomain Sum.swap m) := by
    rw [← Finsupp.mapDomain_comp]; simp
  conv_lhs => rw [hm, MvPolynomial.coeff_rename_mapDomain _ Sum.swap_leftInverse.injective]
  rw [Γ, coeff_homogPart, coeff_homogPart, Finsupp.degree_mapDomain]
  split_ifs with h
  · conv_lhs => rw [← subst_swap_E s i]
    rw [coeff_mapDomain_subst_X_comp Sum.swap_leftInverse.injective]
  · rfl

local notation "T3" => MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) K

noncomputable def bX : Fin d → T3 := fun j => X (Sum.inl j)
noncomputable def bY : Fin d → T3 := fun j => X (Sum.inr (Sum.inl j))
noncomputable def bZ : Fin d → T3 := fun j => X (Sum.inr (Sum.inr j))

noncomputable def FF (a b : Fin d → T3) : Fin d → T3 := fun j => subst (Sum.elim a b) (F.toPowerSeries j)

omit [F.IsComm] in
theorem FF_def (a b : Fin d → T3) : FF (F := F) a b = fun j => subst (Sum.elim a b) (F.toPowerSeries j) := rfl

omit [F.IsComm] in
theorem constantCoeff_FF {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (j : Fin d) : constantCoeff (FF (F := F) a b j) = 0 :=
  constantCoeff_subst_eq_zero (MvFormalGroup.hasSubst_elim ha hb) (by rintro (l | l); exacts [ha l, hb l])
    (F.constantCoeff_eq_zero j)

theorem cbX (j : Fin d) : constantCoeff (bX (K := K) (d := d) j) = 0 := constantCoeff_X _
theorem cbY (j : Fin d) : constantCoeff (bY (K := K) (d := d) j) = 0 := constantCoeff_X _
theorem cbZ (j : Fin d) : constantCoeff (bZ (K := K) (d := d) j) = 0 := constantCoeff_X _

omit [F.IsComm] in

theorem cong_one_FF {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (j : Fin d) : Cong 1 (FF (F := F) a b j) (a j + b j) := by
  have hab := MvFormalGroup.hasSubst_elim ha hb
  have := (cong_one_law F j).substLeft hab (by rintro (l | l); exacts [ha l, hb l])
  simp only [subst_add hab, inlX, inrX, subst_X hab, Sum.elim_inl, Sum.elim_inr] at this
  exact this

theorem cocycle_E (i : Fin d) :
    subst (Sum.elim bX bY) (Edef F s.φ i) + subst (Sum.elim (FF (F := F) bX bY) bZ) (Edef F s.φ i) =
      subst (Sum.elim bY bZ) (Edef F s.φ i) + subst (Sum.elim bX (FF (F := F) bY bZ)) (Edef F s.φ i) := by
  have hFXY := constantCoeff_FF (F := F) cbX cbY
  have hFYZ := constantCoeff_FF (F := F) cbY cbZ
  rw [subst_Edef F s.φ s.const cbX cbY, subst_Edef F s.φ s.const hFXY cbZ, subst_Edef F s.φ s.const cbY cbZ,
    subst_Edef F s.φ s.const cbX hFYZ]
  have hassoc : (fun j => subst (Sum.elim (FF (F := F) bX bY) bZ) (F.toPowerSeries j)) =
      fun j => subst (Sum.elim bX (FF (F := F) bY bZ)) (F.toPowerSeries j) := by
    funext j
    exact MvFormalGroup.subst_elim_assoc (F := F) cbX cbY cbZ j
  rw [hassoc]
  simp only [FF_def]
  ring

omit [F.IsComm] in

theorem coe_aeval {υ τ : Type*} (q : υ → MvPolynomial τ K) (P : MvPolynomial υ K) :
    ((MvPolynomial.aeval q P : MvPolynomial τ K) : MvPowerSeries τ K) =
      MvPolynomial.aeval (fun u => (q u : MvPowerSeries τ K)) P := by
  have h := MvPolynomial.comp_aeval_apply (f := q) (MvPolynomial.coeToMvPowerSeries.algHom K) P
  simpa only [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self, MvPowerSeries.map_id,
    RingHom.id_apply] using h

theorem cocycle_Γ (i : Fin d) :
    MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inr (Sum.inl j)) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
        (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      - MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr (Sum.inl j)) :
          MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      + MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
          (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)) + MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i)
      - MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
          (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)))) (Γ s i) = 0 := by

  set pYZ := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inr (Sum.inl j)) :
      MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpYZ
  set pXYZ := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr (Sum.inl j)) :
      MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K)) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpXYZ
  set pXYZ' := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)) + MvPolynomial.X (Sum.inr (Sum.inr j)))) (Γ s i) with hpXYZ'
  set pXY := MvPolynomial.aeval (Sum.elim (fun j => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j)))) (Γ s i) with hpXY

  have hlin : ∀ (q : Fin d ⊕ Fin d → MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K), (∀ u, (q u).IsHomogeneous 1) →
      (MvPolynomial.aeval q (Γ s i)).IsHomogeneous (n + 2) := fun q hq => by
    simpa using (isHomogeneous_Γ s i).aeval q hq
  have hX1 : ∀ u : Fin d ⊕ (Fin d ⊕ Fin d), (MvPolynomial.X u : MvPolynomial (Fin d ⊕ (Fin d ⊕ Fin d)) K).IsHomogeneous 1 :=
    fun u => MvPolynomial.isHomogeneous_X K u
  have h1 : (pYZ + pXYZ').IsHomogeneous (n + 2) :=
    (hlin _ (by rintro (j | j); exacts [hX1 _, hX1 _])).add (hlin _ (by rintro (j | j); exacts [hX1 _, (hX1 _).add (hX1 _)]))
  have h2 : (pXY + pXYZ).IsHomogeneous (n + 2) :=
    (hlin _ (by rintro (j | j); exacts [hX1 _, hX1 _])).add (hlin _ (by rintro (j | j); exacts [(hX1 _).add (hX1 _), hX1 _]))

  suffices hc : Cong (n + 2) ((pXY + pXYZ : MvPolynomial _ K) : T3) ((pYZ + pXYZ' : MvPolynomial _ K) : T3) by
    have := eq_of_cong_of_isHomogeneous h2 h1 hc
    linear_combination -this

  have hΓsub : ∀ {a b : Fin d → T3} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0),
      Cong (n + 2) (subst (Sum.elim a b) (Edef F s.φ i)) (MvPolynomial.aeval (Sum.elim a b) (Γ s i)) := by
    intro a b ha hb
    have hab := MvFormalGroup.hasSubst_elim ha hb
    have := (cong_E_Γ s i).substLeft hab (by rintro (l | l); exacts [ha l, hb l])
    rwa [subst_coe] at this
  have hFXY := constantCoeff_FF (F := F) cbX cbY
  have hFYZ := constantCoeff_FF (F := F) cbY cbZ
  have e1 : Cong (n + 2) (subst (Sum.elim bX bY) (Edef F s.φ i)) (pXY : T3) := by
    refine (hΓsub cbX cbY).trans (Cong.of_eq ?_)
    rw [hpXY, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have e2 : Cong (n + 2) (subst (Sum.elim (FF (F := F) bX bY) bZ) (Edef F s.φ i)) (pXYZ : T3) := by
    refine (hΓsub hFXY cbZ).trans ?_
    refine (Cong.aeval_of_isHomogeneous (Γ s i) (isHomogeneous_Γ s i) _ (Sum.elim (fun j => bX j + bY j) bZ)
      (by rintro (l | l); exacts [hFXY l, cbZ l]) (by rintro (l | l) <;> simp [bX, bY, bZ])
      (by rintro (l | l); exacts [cong_one_FF cbX cbY l, Cong.refl _])).trans (Cong.of_eq ?_)
    rw [hpXYZ, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have e3 : Cong (n + 2) (subst (Sum.elim bY bZ) (Edef F s.φ i)) (pYZ : T3) := by
    refine (hΓsub cbY cbZ).trans (Cong.of_eq ?_)
    rw [hpYZ, coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have e4 : Cong (n + 2) (subst (Sum.elim bX (FF (F := F) bY bZ)) (Edef F s.φ i)) (pXYZ' : T3) := by
    refine (hΓsub cbX hFYZ).trans ?_
    refine (Cong.aeval_of_isHomogeneous (Γ s i) (isHomogeneous_Γ s i) _ (Sum.elim bX (fun j => bY j + bZ j))
      (by rintro (l | l); exacts [cbX l, hFYZ l]) (by rintro (l | l) <;> simp [bX, bY, bZ])
      (by rintro (l | l); exacts [Cong.refl _, cong_one_FF cbY cbZ l])).trans (Cong.of_eq ?_)
    rw [hpXYZ', coe_aeval]
    exact congrArg (fun f : Fin d ⊕ Fin d → T3 => (MvPolynomial.aeval f (Γ s i) : T3))
      (funext fun u => by rcases u with j | j <;> simp [bX, bY, bZ])
  have := (e1.add e2).symm.trans ((Cong.of_eq (cocycle_E s i)).trans (e3.add e4))
  simpa only [MvPolynomial.coe_add] using this

end Step

end Lazard

section Construct

variable {K : Type*} [CommRing K] {d : ℕ} {F : MvFormalGroup d K} [F.IsComm]
  (hK : ∀ n : ℕ, IsUnit ((n + 1 : ℕ) : K))

section
variable {n : ℕ} (s : Stage F (n + 1))

include hK in
theorem exists_corr (i : Fin d) : ∃ h : MvPolynomial (Fin d) K, h.IsHomogeneous (n + 2) ∧
    Γ s i = MvPolynomial.aeval (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Fin d ⊕ Fin d) K)) h - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h :=
  MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric (n + 2) (hK (n + 1))
    (Γ s i) (isHomogeneous_Γ s i) (rename_swap_Γ s i) (cocycle_Γ s i)

noncomputable def corr (i : Fin d) : MvPolynomial (Fin d) K := Classical.choose (exists_corr hK s i)

theorem isHomogeneous_corr (i : Fin d) : (corr hK s i).IsHomogeneous (n + 2) := (Classical.choose_spec (exists_corr hK s i)).1

theorem Γ_eq_delta_corr (i : Fin d) : Γ s i = MvPolynomial.aeval (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Fin d ⊕ Fin d) K)) (corr hK s i) - MvPolynomial.rename Sum.inl (corr hK s i)
      - MvPolynomial.rename Sum.inr (corr hK s i) := (Classical.choose_spec (exists_corr hK s i)).2

theorem cong_corr_zero (i : Fin d) : Cong (n + 1) (corr hK s i : MvPowerSeries (Fin d) K) 0 := fun m hm => by
  rw [MvPolynomial.coeff_coe, map_zero, (isHomogeneous_corr hK s i).coeff_eq_zero (by omega)]

theorem cong_E_corr (i : Fin d) :
    Cong (n + 2) (Edef F (fun i => (corr hK s i : MvPowerSeries (Fin d) K)) i) (Γ s i : MvPolynomial (Fin d ⊕ Fin d) K) := by
  have hplus : subst F.toPowerSeries (corr hK s i : MvPowerSeries (Fin d) K) =
      MvPolynomial.aeval F.toPowerSeries (corr hK s i) := subst_coe _
  have h1 : Cong (n + 2) (subst F.toPowerSeries (corr hK s i : MvPowerSeries (Fin d) K))
      ((MvPolynomial.aeval (fun j => (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j) :
        MvPolynomial (Fin d ⊕ Fin d) K)) (corr hK s i) : MvPolynomial (Fin d ⊕ Fin d) K) : MvPowerSeries (Fin d ⊕ Fin d) K) := by
    rw [hplus, coe_aeval]
    refine (Cong.aeval_of_isHomogeneous _ (isHomogeneous_corr hK s i) _ _ F.constantCoeff_eq_zero
      (fun j => by simp) (fun j => ?_))
    have := cong_one_law F j
    simpa [inlX, inrX] using this
  have h2 : subst inlX (corr hK s i : MvPowerSeries (Fin d) K) =
      ((MvPolynomial.rename (Sum.inl : Fin d → Fin d ⊕ Fin d) (corr hK s i) : MvPolynomial (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d ⊕ Fin d) K) := by
    rw [subst_coe, show MvPolynomial.rename (Sum.inl : Fin d → Fin d ⊕ Fin d) (corr hK s i) =
      MvPolynomial.aeval (fun j => MvPolynomial.X (Sum.inl j)) (corr hK s i) from by
        rw [MvPolynomial.rename_eq_aeval]; rfl, coe_aeval]
    exact congrArg (fun q : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K => MvPolynomial.aeval q (corr hK s i))
      (funext fun u => by simp [inlX])
  have h3 : subst inrX (corr hK s i : MvPowerSeries (Fin d) K) =
      ((MvPolynomial.rename (Sum.inr : Fin d → Fin d ⊕ Fin d) (corr hK s i) : MvPolynomial (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d ⊕ Fin d) K) := by
    rw [subst_coe, show MvPolynomial.rename (Sum.inr : Fin d → Fin d ⊕ Fin d) (corr hK s i) =
      MvPolynomial.aeval (fun j => MvPolynomial.X (Sum.inr j)) (corr hK s i) from by
        rw [MvPolynomial.rename_eq_aeval]; rfl, coe_aeval]
    exact congrArg (fun q : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K => MvPolynomial.aeval q (corr hK s i))
      (funext fun u => by simp [inrX])
  have coe_sub' : ∀ P Q : MvPolynomial (Fin d ⊕ Fin d) K,
      ((P - Q : MvPolynomial (Fin d ⊕ Fin d) K) : MvPowerSeries (Fin d ⊕ Fin d) K) = (P : MvPowerSeries (Fin d ⊕ Fin d) K) - Q :=
    fun P Q => by simpa using map_sub (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin d ⊕ Fin d) (R := K)) P Q
  rw [Edef, h2, h3, Γ_eq_delta_corr hK s i, coe_sub', coe_sub']
  exact (h1.sub (Cong.refl _)).sub (Cong.refl _)

omit [F.IsComm] in

theorem Edef_sub (φ ψ : Fin d → MvPowerSeries (Fin d) K) (i : Fin d) :
    Edef F (fun i => φ i - ψ i) i = Edef F φ i - Edef F ψ i := by
  simp only [Edef, subst_sub F.hasSubst_toPowerSeries, subst_sub (hasSubst_of_constantCoeff_zero constantCoeff_inlX),
    subst_sub (hasSubst_of_constantCoeff_zero constantCoeff_inrX)]
  ring

noncomputable def step : Stage F (n + 2) where
  φ := fun i => s.φ i - (corr hK s i : MvPowerSeries (Fin d) K)
  const := fun i => by
    rw [map_sub, s.const, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
      (isHomogeneous_corr hK s i).coeff_eq_zero (by simp), sub_zero]
  lin := fun i => by
    have := (s.lin i).sub (cong_corr_zero hK s i |>.mono (by omega))
    rwa [sub_zero] at this
  addit := fun i => by
    rw [Edef_sub]
    have := (cong_E_Γ s i).sub (cong_E_corr hK s i)
    rwa [sub_self] at this

theorem step_cong (i : Fin d) : Cong (n + 1) ((step hK s).φ i) (s.φ i) := by
  have := (Cong.refl (s.φ i)).sub (cong_corr_zero hK s i)
  rwa [sub_zero] at this

end

variable (F) in

noncomputable def stages : (k : ℕ) → Stage F (k + 1)
  | 0 => stageOne F
  | k + 1 => step hK (stages k)

theorem stages_cong {k l : ℕ} (hkl : k ≤ l) (i : Fin d) : Cong (k + 1) ((stages F hK l).φ i) ((stages F hK k).φ i) := by
  induction l with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact Cong.refl _
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with hlt | hge
    · exact ((step_cong hK (stages F hK l) i).mono (by omega)).trans (ih (by omega))
    · obtain rfl : k = l + 1 := by omega
      exact Cong.refl _

variable (F) in

noncomputable def logK (i : Fin d) : MvPowerSeries (Fin d) K := fun m => coeff m ((stages F hK m.degree).φ i)

theorem coeff_logK (i : Fin d) (m : Fin d →₀ ℕ) : coeff m (logK F hK i) = coeff m ((stages F hK m.degree).φ i) := rfl

theorem cong_logK (N : ℕ) (i : Fin d) : Cong (N + 1) (logK F hK i) ((stages F hK N).φ i) := by
  intro m hm
  rw [coeff_logK]
  rcases Nat.lt_or_ge m.degree (N + 1) with hlt | hge
  · exact ((stages_cong hK (show m.degree ≤ N by omega) i) m (Nat.le_succ _)).symm
  · have hdeg : m.degree = N + 1 := by omega
    rw [hdeg]
    exact (stages_cong hK (Nat.le_succ N) i) m (by omega)

theorem constantCoeff_logK (i : Fin d) : constantCoeff (logK F hK i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logK, coeff_zero_eq_constantCoeff_apply]
  exact (stages F hK _).const i

theorem cong_one_logK (i : Fin d) : Cong 1 (logK F hK i) (X i) :=
  (cong_logK hK 0 i).trans ((stages F hK 0).lin i)

omit [F.IsComm] in
theorem Edef_cong {N : ℕ} {φ ψ : Fin d → MvPowerSeries (Fin d) K} (h : ∀ i, Cong N (φ i) (ψ i)) (i : Fin d) :
    Cong N (Edef F φ i) (Edef F ψ i) :=
  (((h i).substLeft F.hasSubst_toPowerSeries F.constantCoeff_eq_zero).sub
    ((h i).substLeft (hasSubst_of_constantCoeff_zero constantCoeff_inlX) constantCoeff_inlX)).sub
    ((h i).substLeft (hasSubst_of_constantCoeff_zero constantCoeff_inrX) constantCoeff_inrX)

theorem Edef_logK (i : Fin d) : Edef F (logK F hK) i = 0 := by
  ext m
  rw [map_zero]
  have h1 := Edef_cong (F := F) (cong_logK (F := F) hK m.degree) i
  have h2 := (stages F hK m.degree).addit i
  rw [h1 m (by omega), h2 m (by omega), map_zero]

end Construct

section Weighted

variable {S : Type*} [CommRing S] {σ : Type*}

def CongW (w : σ → ℕ) (n : ℕ) (f g : MvPowerSeries σ S) : Prop :=
  ∀ m : σ →₀ ℕ, Finsupp.weight w m ≤ n → coeff m f = coeff m g

namespace CongW
variable {w : σ → ℕ} {n : ℕ} {f g : MvPowerSeries σ S}

theorem refl (f : MvPowerSeries σ S) : CongW w n f f := fun _ _ => rfl

theorem mul {f' g' : MvPowerSeries σ S} (h₁ : CongW w n f g) (h₂ : CongW w n f' g') : CongW w n (f * f') (g * g') := by
  classical
  intro m hm
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h1 : Finsupp.weight w x.1 ≤ n := by
    have := congrArg (Finsupp.weight w) hx'; rw [map_add] at this; omega
  have h2 : Finsupp.weight w x.2 ≤ n := by
    have := congrArg (Finsupp.weight w) hx'; rw [map_add] at this; omega
  rw [h₁ _ h1, h₂ _ h2]

theorem pow (h₁ : CongW w n f g) (k : ℕ) : CongW w n (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero]; exact refl _
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h₁

theorem finsuppProd {ι : Type*} (d : ι →₀ ℕ) {F G : ι → MvPowerSeries σ S} (h : ∀ i, CongW w n (F i) (G i)) :
    CongW w n (d.prod fun i e => F i ^ e) (d.prod fun i e => G i ^ e) := by
  classical
  rw [Finsupp.prod, Finsupp.prod]
  induction d.support using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact ((h a).pow _).mul ih

theorem substRight {τ : Type*} {a b : τ → MvPowerSeries σ S} (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, CongW w n (a i) (b i)) (F : MvPowerSeries τ S) : CongW w n (subst a F) (subst b F) := by
  intro m hm
  rw [coeff_subst ha, coeff_subst hb]
  exact finsum_congr fun d => by rw [(finsuppProd d hab) m hm]

end CongW

variable {κ : Type*}

def wY : σ ⊕ κ → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem weight_wY_sumElim (m : σ →₀ ℕ) (c : κ →₀ ℕ) : Finsupp.weight (wY (σ := σ) (κ := κ)) (m.sumElim c) = c.degree := by
  classical
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj
    Sum.inl_injective, Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
  simp [wY, Finsupp.degree_apply, Finsupp.sum]

noncomputable def emb (a : MvPowerSeries σ S) : MvPowerSeries (σ ⊕ κ) S :=
  subst (fun t => (X (Sum.inl t) : MvPowerSeries (σ ⊕ κ) S)) a

theorem hasSubst_X_comp {τ : Type*} {e : σ → τ} (he : Function.Injective e) :
    HasSubst (fun s => (X (e s) : MvPowerSeries τ S)) := by
  classical
  refine ⟨fun s => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d' => ?_⟩
  apply Set.Subsingleton.finite
  intro s₁ h₁ s₂ h₂
  simp only [Set.mem_setOf_eq, coeff_X] at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  · rw [e₁] at e₂; exact he (Finsupp.single_left_injective one_ne_zero e₂)
  all_goals simp_all

theorem coeff_subst_X_comp_eq_zero {τ : Type*} {e : σ → τ} (he : Function.Injective e) (g : MvPowerSeries σ S)
    (n : τ →₀ ℕ) (hn : ∀ d : σ →₀ ℕ, n ≠ Finsupp.mapDomain e d) :
    coeff n (subst (fun s => (X (e s) : MvPowerSeries τ S)) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_X_comp he), finsum_eq_zero_of_forall_eq_zero]
  intro d
  rw [show (d.prod fun s k => (X (e s) : MvPowerSeries τ S) ^ k) = monomial (d.mapDomain e) 1 by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_mapDomain_index_inj he], coeff_monomial, if_neg (hn d), smul_zero]

theorem mapDomain_inl_eq_sumElim (m : σ →₀ ℕ) : m.mapDomain Sum.inl = m.sumElim (0 : κ →₀ ℕ) := by
  rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_zero, add_zero]

theorem mapDomain_inr_eq_sumElim (c : κ →₀ ℕ) : c.mapDomain Sum.inr = (0 : σ →₀ ℕ).sumElim c := by
  rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_zero, zero_add]

theorem coeff_sumElim_zero_emb (a : MvPowerSeries σ S) (m : σ →₀ ℕ) : coeff (m.sumElim (0 : κ →₀ ℕ)) (emb a) = coeff m a := by
  rw [emb, ← mapDomain_inl_eq_sumElim, coeff_mapDomain_subst_X_comp Sum.inl_injective]

theorem coeff_sumElim_emb_eq_zero (a : MvPowerSeries σ S) (m : σ →₀ ℕ) {c : κ →₀ ℕ} (hc : c ≠ 0) :
    coeff (m.sumElim c) (emb a) = 0 := by
  apply coeff_subst_X_comp_eq_zero Sum.inl_injective
  intro d' h
  apply hc
  have := congrArg (fun n => Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn) h
  simpa [mapDomain_inl_eq_sumElim] using this

variable [Fintype κ]

noncomputable def linY (g : MvPowerSeries (σ ⊕ κ) S) : MvPowerSeries (σ ⊕ κ) S :=
  emb (fun m => coeff (m.sumElim 0) g) + ∑ k, X (Sum.inr k) * emb (fun m => coeff (m.sumElim (Finsupp.single k 1)) g)

theorem coeff_X_inr_mul (k : κ) (g : MvPowerSeries (σ ⊕ κ) S) (m : σ →₀ ℕ) (c : κ →₀ ℕ) :
    coeff (m.sumElim c) (X (Sum.inr k) * g) = if Finsupp.single k 1 ≤ c then coeff (m.sumElim (c - Finsupp.single k 1)) g else 0 := by
  classical
  rw [X_def, ← Finsupp.sumElim_zero_single, coeff_monomial_mul]
  have hiff : (0 : σ →₀ ℕ).sumElim (Finsupp.single k 1) ≤ m.sumElim c ↔ Finsupp.single k 1 ≤ c := by
    simp only [Finsupp.le_def]
    constructor
    · intro h k'; simpa [Finsupp.single_apply] using h (Sum.inr k')
    · rintro h (t | k')
      · simp [Finsupp.single_apply]
      · simpa [Finsupp.single_apply] using h k'
  by_cases h : Finsupp.single k 1 ≤ c
  · rw [if_pos (hiff.2 h), if_pos h, one_mul]
    congr 2
    ext u; rcases u with t | k' <;> simp [Finsupp.single_apply]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem congW_linY (g : MvPowerSeries (σ ⊕ κ) S) : CongW wY 1 g (linY g) := by
  classical
  intro n hn
  obtain ⟨m, c, rfl⟩ : ∃ (m : σ →₀ ℕ) (c : κ →₀ ℕ), n = m.sumElim c :=
    ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain n).symm⟩
  rw [weight_wY_sumElim] at hn
  rw [linY, map_add, map_sum]
  rcases Nat.lt_or_ge c.degree 1 with h0 | h1
  · have hc : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    subst hc
    rw [coeff_sumElim_zero_emb, Finset.sum_eq_zero fun k _ => ?_, add_zero]
    · rfl
    · rw [coeff_X_inr_mul, if_neg]; intro h; have := h k; simp at this
  · obtain ⟨k, rfl⟩ := exists_eq_single_of_degree_eq_one (m := c) (by omega)
    rw [coeff_sumElim_emb_eq_zero _ _ (by simp), zero_add, Finset.sum_eq_single k]
    · rw [coeff_X_inr_mul, if_pos le_rfl, tsub_self, coeff_sumElim_zero_emb]; rfl
    · intro k' _ hk'
      rw [coeff_X_inr_mul, if_neg]
      intro h; have := h k'; simp [Finsupp.single_apply, hk'] at this
    · intro hk; exact absurd (Finset.mem_univ k) hk

omit [Fintype κ] in
theorem constantCoeff_emb (a : MvPowerSeries σ S) (ha : constantCoeff a = 0) : constantCoeff (emb (κ := κ) a) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_X_comp Sum.inl_injective) (fun t => constantCoeff_X _) ha

end Weighted

section Honda

variable {𝓞 : Type*} [CommRing 𝓞] {K : Type*} [CommRing K] (φ : 𝓞 →+* K) {d : ℕ} (F𝓞 : MvFormalGroup d 𝓞)

theorem coeff_subst_elim_X_zero {S : Type*} [CommRing S] {σ κ : Type*} (g : MvPowerSeries (σ ⊕ κ) S) (m : σ →₀ ℕ) :
    coeff m (subst (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ => 0)) g) = coeff (m.sumElim 0) g := by
  classical
  have ha : HasSubst (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ : κ => 0)) := by
    refine ⟨?_, fun d => ?_⟩
    · rintro (t | k')
      · simp only [Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
      · simp only [Sum.elim_inr, map_zero]; exact IsNilpotent.zero
    · apply Set.Subsingleton.finite
      rintro (t₁ | k₁) h₁ (t₂ | k₂) h₂ <;>
        simp only [Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr, coeff_X, map_zero, ne_eq, not_true_eq_false] at h₁ h₂
      split_ifs at h₁ h₂ with e₁ e₂
      · rw [e₁] at e₂; rw [Finsupp.single_left_injective one_ne_zero e₂]
      all_goals simp_all
  have key : ∀ n : σ ⊕ κ →₀ ℕ, coeff m (n.prod fun u e => (Sum.elim (fun t => (X t : MvPowerSeries σ S)) (fun _ => 0) u) ^ e) =
      if n = m.sumElim 0 then 1 else 0 := by
    intro n
    set nτ : σ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
    set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
    have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
    have hsplit : (nτ.sumElim nκ = m.sumElim 0 ↔ m = nτ ∧ nκ = 0) := by
      constructor
      · intro h
        exact ⟨Eq.symm (by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
          by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
    rw [hn, Finsupp.prod_sumElim]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← MvPowerSeries.monomial_one_eq]
    have hY : (nκ.prod fun _ e => ((0 : MvPowerSeries σ S)) ^ e) = if nκ = 0 then 1 else 0 := by
      by_cases h0 : nκ = 0
      · rw [h0, if_pos rfl, Finsupp.prod_zero_index]
      · rw [if_neg h0]
        obtain ⟨k', hk'⟩ := Finsupp.support_nonempty_iff.2 h0
        rw [Finsupp.prod, Finset.prod_eq_zero hk' (by rw [zero_pow (Finsupp.mem_support_iff.1 hk')])]
    rw [hY]
    simp only [hsplit]
    clear_value nτ nκ
    clear hY hn hnτ hnκ hsplit
    split_ifs <;> simp_all [coeff_monomial]
  rw [coeff_subst ha, finsum_eq_single _ (m.sumElim 0)]
  · rw [key, if_pos rfl, smul_eq_mul, mul_one]
  · intro n hn
    rw [key, if_neg hn, smul_zero]

theorem coeff_sumElim_zero_law {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j : Fin d) (m : Fin d →₀ ℕ) :
    coeff (m.sumElim 0) (G.toPowerSeries j) = coeff m (X j : MvPowerSeries (Fin d) S) := by
  rw [← coeff_subst_elim_X_zero, MvFormalGroup.subst_elim_X_zero]

noncomputable def Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin d) : MvPowerSeries (Fin d) S :=
  fun m => coeff (m.sumElim (Finsupp.single k 1)) (G.toPowerSeries j)

theorem coeff_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin d) (m : Fin d →₀ ℕ) :
    coeff m (Psi G j k) = coeff (m.sumElim (Finsupp.single k 1)) (G.toPowerSeries j) := rfl

theorem constantCoeff_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) (j k : Fin d) :
    constantCoeff (Psi G j k) = if j = k then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Psi, Finsupp.sumElim_zero_single, G.coeff_single_inr]

theorem Psi_map (j k : Fin d) : Psi (F𝓞.map φ) j k = MvPowerSeries.map φ (Psi F𝓞 j k) := by
  ext m
  rw [coeff_Psi, coeff_map, coeff_Psi]
  show coeff _ (MvPowerSeries.map φ (F𝓞.toPowerSeries j)) = _
  rw [coeff_map]

theorem isUnit_det_Psi {S : Type*} [CommRing S] (G : MvFormalGroup d S) :
    IsUnit (Matrix.det (Matrix.of fun j k => Psi G j k)) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (RingHom.mapMatrix (constantCoeff : MvPowerSeries (Fin d) S →+* S)) (Matrix.of fun j k => Psi G j k) = 1 := by
    ext j k
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_Psi, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

variable (f : Fin d → MvPowerSeries (Fin d) K) (hf0 : ∀ i, constantCoeff (f i) = 0) (hf1 : ∀ i, Cong 1 (f i) (X i))
  (hfadd : ∀ i, subst (F𝓞.map φ).toPowerSeries (f i) = subst inlX (f i) + subst inrX (f i))

noncomputable def Dlog (i j : Fin d) : MvPowerSeries (Fin d) K :=
  fun m => ((m j + 1 : ℕ) : K) * coeff (m + Finsupp.single j 1) (f i)

include hf0 hf1 hfadd in

theorem sum_Dlog_mul_Psi (i k : Fin d) : ∑ j, Psi (F𝓞.map φ) j k * Dlog f i j = if i = k then 1 else 0 := by
  classical
  set F := F𝓞.map φ with hF

  set A : Fin d → MvPowerSeries (Fin d) K := fun j m => coeff (m.sumElim (0 : Fin d →₀ ℕ)) (F.toPowerSeries j) with hA
  have hAX : A = fun j => X j := by funext j; ext m; exact coeff_sumElim_zero_law F j m
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by rw [hAX]; exact constantCoeff_X j
  set G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K := fun j =>
    subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) (A j) +
      ∑ k', X (Sum.inr k') * subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) (Psi F j k') with hG
  have hGlin : ∀ j, G j = linY (F.toPowerSeries j) := fun j => rfl
  have hG0 : ∀ j, constantCoeff (G j) = 0 := fun j => by
    rw [hG]; dsimp only
    rw [map_add, map_sum]
    rw [show subst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) (A j) = emb (A j) from rfl,
      constantCoeff_emb _ (hA0 j), zero_add]
    exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]
  have hGs : HasSubst G := hasSubst_of_constantCoeff_zero hG0

  have taylor := fun m => MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq (f i) (Dlog f i)
    (fun j m => rfl) A hA0 (fun j k' => Psi F j k') m k

  have hFG : ∀ m : Fin d →₀ ℕ, coeff (m.sumElim (Finsupp.single k 1)) (subst F.toPowerSeries (f i)) =
      coeff (m.sumElim (Finsupp.single k 1)) (subst G (f i)) := fun m =>
    (CongW.substRight F.hasSubst_toPowerSeries hGs (fun j => by rw [hGlin]; exact congW_linY _) (f i)) _
      (by rw [weight_wY_sumElim, Finsupp.degree_single])

  have hLHS : ∀ m : Fin d →₀ ℕ, coeff (m.sumElim (Finsupp.single k 1)) (subst F.toPowerSeries (f i)) =
      if m = 0 then (if i = k then 1 else 0) else 0 := by
    intro m
    rw [hfadd, map_add, show subst inlX (f i) = emb (f i) from rfl, coeff_sumElim_emb_eq_zero _ _ (by simp), zero_add]
    unfold inrX
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl, ← mapDomain_inr_eq_sumElim, coeff_mapDomain_subst_X_comp Sum.inr_injective, (hf1 i) _
        (by rw [Finsupp.degree_single]), coeff_X]
      by_cases hik : i = k
      · subst hik; simp
      · rw [if_neg hik, if_neg (fun h => hik (Finsupp.single_left_injective one_ne_zero h).symm)]
    · rw [if_neg hm]
      apply coeff_subst_X_comp_eq_zero Sum.inr_injective
      intro d' h
      apply hm
      have := congrArg (fun n => Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn) h
      simpa [mapDomain_inr_eq_sumElim] using this

  ext m
  have := (hLHS m).symm.trans ((hFG m).trans (taylor m))
  rw [hAX] at this
  simp only [show (fun j => (X j : MvPowerSeries (Fin d) K)) = X from rfl,
    show ∀ g : MvPowerSeries (Fin d) K, subst (X : Fin d → MvPowerSeries (Fin d) K) g = g from
      fun g => congrFun subst_self g] at this
  rw [← this]
  split_ifs <;> simp [coeff_one, *]

include hf0 hf1 hfadd in

theorem exists_coeff_Dlog (i j : Fin d) (m : Fin d →₀ ℕ) : ∃ c : 𝓞, φ c = coeff m (Dlog f i j) := by
  classical
  set ΨO : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) 𝓞) := Matrix.of fun j k => Psi F𝓞 j k with hΨO
  set ΨK : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) K) := Matrix.of fun j k => Psi (F𝓞.map φ) j k with hΨK
  set D : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) K) := Matrix.of fun i j => Dlog f i j with hD
  have hmap : ΨK = (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO := by
    ext j k; simp [hΨK, hΨO, RingHom.mapMatrix_apply, Matrix.map_apply, Psi_map]
  have hDΨ : D * ΨK = 1 := by
    refine Matrix.ext fun i k => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hD, hΨK, Matrix.of_apply]
    rw [← sum_Dlog_mul_Psi φ F𝓞 f hf0 hf1 hfadd i k]
    exact Finset.sum_congr rfl fun j _ => mul_comm (Dlog f i j) (Psi (F𝓞.map φ) j k)
  have hunit := isUnit_det_Psi F𝓞
  have hD' : D = (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO⁻¹ := by
    calc D = D * (RingHom.mapMatrix (MvPowerSeries.map φ)) (ΨO * ΨO⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hunit, map_one, mul_one]
      _ = D * ΨK * (RingHom.mapMatrix (MvPowerSeries.map φ)) ΨO⁻¹ := by rw [map_mul, ← hmap, mul_assoc]
      _ = _ := by rw [hDΨ, one_mul]
  refine ⟨coeff m ((ΨO⁻¹) i j), ?_⟩
  have := congrFun (congrFun hD' i) j
  simp only [hD, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at this
  rw [this, coeff_map]

end Honda

section UnitsSec

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

theorem isUnit_natCast_of_not_dvd [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : 𝓞)) := by
  have hcop : IsCoprime (n : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : 𝓞) * n + (b : 𝓞) * p = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hab
    simpa using this
  have hjac : (b : 𝓞) * p ∈ (⊥ : Ideal 𝓞).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : 𝓞)}) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  have hu : IsUnit ((a : 𝓞) * n) := by
    rw [Ideal.mem_jacobson_bot] at hjac
    have := hjac (-1)
    rwa [show (b : 𝓞) * p * (-1) + 1 = (a : 𝓞) * n by linear_combination (-1 : 𝓞) * h1] at this
  exact isUnit_of_mul_isUnit_right hu

theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega

theorem two_mul_le_of_pow_mul {k u n : ℕ} (hu : u ≠ 0) (h : n = p ^ k * u) : 2 * k ≤ n := by
  have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
  have h2 : p ^ k ≤ n := by rw [h]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu)
  have := two_mul_le_two_pow k
  omega

end UnitsSec

section Rescale

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*}

noncomputable def rho (p : ℕ) : MvPowerSeries σ 𝓞 →+* MvPowerSeries σ 𝓞 := rescale (fun _ => (p : 𝓞))

theorem coeff_rho (p : ℕ) (f : MvPowerSeries σ 𝓞) (m : σ →₀ ℕ) :
    coeff m (rho p f) = (p : 𝓞) ^ m.degree * coeff m f := by
  rw [rho, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

theorem rho_eq_subst (p : ℕ) (f : MvPowerSeries σ 𝓞) :
    rho p f = subst ((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) f :=
  rescale_eq_subst _ f

theorem rho_X (p : ℕ) (s : σ) : rho (𝓞 := 𝓞) p (X s) = (p : 𝓞) • X s := by
  rw [rho_eq_subst, subst_X (HasSubst.smul_X _)]
  rfl

theorem rho_subst (p : ℕ) {τ : Type*} {a : τ → MvPowerSeries σ 𝓞} (ha : HasSubst a) (f : MvPowerSeries τ 𝓞) :
    rho p (subst a f) = subst (fun t => rho p (a t)) f := by
  rw [rho_eq_subst, subst_comp_subst_apply ha (HasSubst.smul_X _)]
  congr 1
  funext t
  rw [rho_eq_subst]

theorem subst_smul_family (p : ℕ) {τ : Type*} {a : σ → MvPowerSeries τ 𝓞} (ha : HasSubst a) (f : MvPowerSeries σ 𝓞) :
    subst (fun s => (p : 𝓞) • a s) f = subst a (rho p f) := by
  rw [rho_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext s
  show (p : 𝓞) • a s = subst a (((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) s)
  rw [Pi.smul_apply', subst_smul ha, subst_X ha]

end Rescale

section Descent

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

local notation "K" => Localization.Away (p : 𝓞)
local notation "φ" => algebraMap 𝓞 (Localization.Away (p : 𝓞))

include hpR in
theorem φ_injective : Function.Injective φ :=
  IsLocalization.injective (M := Submonoid.powers (p : 𝓞)) (Localization.Away (p : 𝓞)) (Submonoid.powers_le.2 hpR)

theorem isUnit_φp : IsUnit (φ (p : 𝓞)) := IsLocalization.Away.algebraMap_isUnit (p : 𝓞)

theorem isUnit_succ (n : ℕ) : IsUnit ((n + 1 : ℕ) : K) := by
  obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n + 1 ≠ 0 by omega) p hp.out.ne_one
  rw [hk, Nat.cast_mul, Nat.cast_pow]
  refine IsUnit.mul (IsUnit.pow _ ?_) ?_
  · have := isUnit_φp (𝓞 := 𝓞) p; rwa [map_natCast] at this
  · have := (isUnit_natCast_of_not_dvd (𝓞 := 𝓞) p hu).map φ; rwa [map_natCast] at this

scoped instance isComm_map {S : Type*} [CommRing S] (g : 𝓞 →+* S) : (F.map g).IsComm where
  comm := fun i => by
    have h := congrArg (MvPowerSeries.map g) (MvFormalGroup.IsComm.comm (F := F) i)
    rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X]))] at h
    have hfam : (fun s => MvPowerSeries.map g (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        (fun j => X (Sum.inl j)) s)) = Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) S)) (fun j => X (Sum.inl j)) := by
      funext s; rcases s with j | j <;> simp
    rw [hfam] at h
    exact h

noncomputable def fK : Fin d → MvPowerSeries (Fin d) K := logK (F.map φ) (isUnit_succ p)

theorem fK_const (i : Fin d) : constantCoeff (fK p F i) = 0 := constantCoeff_logK _ i
theorem fK_lin (i : Fin d) : Cong 1 (fK p F i) (X i) := cong_one_logK _ i
theorem fK_add (i : Fin d) : subst (F.map φ).toPowerSeries (fK p F i) = subst inlX (fK p F i) + subst inrX (fK p F i) := by
  have := Edef_logK (F := F.map φ) (isUnit_succ p) i
  rw [Edef] at this
  unfold fK
  linear_combination this

include hpR in

theorem exists_pre (i : Fin d) (m : Fin d →₀ ℕ) (hm : m ≠ 0) :
    ∃ c : 𝓞, φ c = φ (p : 𝓞) ^ (m.degree - 1) * coeff m (fK p F i) ∧
      ∃ k : ℕ, 2 * k ≤ m.degree ∧ c ∈ Ideal.span {(p : 𝓞) ^ (m.degree - 1 - k)} := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    exact hm (Finsupp.ext fun j => not_not.1 (not_exists.1 h j))
  obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj p hp.out.ne_one
  have hu0 : u ≠ 0 := fun h => hj (by rw [hk, h, mul_zero])

  set m' := m - Finsupp.single j 1 with hm'
  have hmm' : m' + Finsupp.single j 1 = m := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hj))
  have hmj : m' j + 1 = m j := by
    have := congrArg (fun n => n j) hmm'; simpa using this
  obtain ⟨c₀, hc₀⟩ := exists_coeff_Dlog φ F (fK p F) (fK_const p F) (fK_lin p F) (fK_add p F) i j m'
  rw [show coeff m' (Dlog (fK p F) i j) = ((m' j + 1 : ℕ) : K) * coeff (m' + Finsupp.single j 1) (fK p F i) from rfl,
    hmj, hmm', hk, Nat.cast_mul, Nat.cast_pow] at hc₀

  obtain ⟨uu, huu⟩ := isUnit_natCast_of_not_dvd (𝓞 := 𝓞) p hu
  have hkdeg : k ≤ m.degree - 1 := by
    have h2 := two_mul_le_of_pow_mul p hu0 hk
    have h3 : m j ≤ m.degree := Finsupp.le_degree j m
    have : 0 < m j := Nat.pos_of_ne_zero hj
    omega
  refine ⟨(p : 𝓞) ^ (m.degree - 1 - k) * c₀ * ↑uu⁻¹, ?_, k, ?_, ?_⟩
  · rw [map_mul, map_mul, map_pow, hc₀, map_natCast]
    have huK : (u : K) * φ (↑uu⁻¹ : 𝓞) = 1 := by rw [← map_natCast φ u, ← map_mul, ← huu, Units.mul_inv, map_one]
    have hpk : (p : K) ^ (m.degree - 1) = (p : K) ^ (m.degree - 1 - k) * (p : K) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkdeg]
    rw [hpk]
    linear_combination ((p : K) ^ (m.degree - 1 - k) * (p : K) ^ k * coeff m (fK p F i)) * huK
  · have h2 := two_mul_le_of_pow_mul p hu0 hk
    exact h2.trans (Finsupp.le_degree j m)
  · rw [mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

noncomputable def bcoef (i : Fin d) (m : Fin d →₀ ℕ) : 𝓞 :=
  if hm : m = 0 then 0 else Classical.choose (exists_pre p hpR F i m hm)

theorem φ_bcoef (i : Fin d) (m : Fin d →₀ ℕ) :
    φ (bcoef p hpR F i m) = φ (p : 𝓞) ^ (m.degree - 1) * coeff m (fK p F i) := by
  rw [bcoef]
  split_ifs with hm
  · rw [hm, map_zero, coeff_zero_eq_constantCoeff_apply, fK_const, mul_zero]
  · exact (Classical.choose_spec (exists_pre p hpR F i m hm)).1

include hpR in
theorem bcoef_mem (i : Fin d) (m : Fin d →₀ ℕ) (N : ℕ) (hN : 2 * N + 2 ≤ m.degree) :
    bcoef p hpR F i m ∈ Ideal.span {(p : 𝓞) ^ N} := by
  have hm : m ≠ 0 := by rintro rfl; simp at hN
  obtain ⟨c, hc, k, hk, hmem⟩ := exists_pre p hpR F i m hm
  have hcb : c = bcoef p hpR F i m := φ_injective p hpR (by rw [hc, φ_bcoef])
  rw [← hcb]
  refine Ideal.span_singleton_le_span_singleton.2 ?_ hmem
  exact pow_dvd_pow _ (by omega)

noncomputable def phiSer (i : Fin d) : MvPowerSeries (Fin d) 𝓞 := fun m => bcoef p hpR F i m

open Classical in
noncomputable def FpSer (i : Fin d) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
  fun m => if m = 0 then 0 else (p : 𝓞) ^ (m.degree - 1) * coeff m (F.toPowerSeries i)

theorem coeff_phiSer (i : Fin d) (m : Fin d →₀ ℕ) : coeff m (phiSer p hpR F i) = bcoef p hpR F i m := rfl

open Classical in
theorem coeff_FpSer (i : Fin d) (m : Fin d ⊕ Fin d →₀ ℕ) :
    coeff m (FpSer p F i) = if m = 0 then 0 else (p : 𝓞) ^ (m.degree - 1) * coeff m (F.toPowerSeries i) := rfl

noncomputable def π : Kˣ := (isUnit_φp (𝓞 := 𝓞) p).unit

theorem π_val : ((π p : Kˣ) : K) = (p : K) := by rw [π, IsUnit.unit_spec, map_natCast]

theorem map_phiSer (i : Fin d) : MvPowerSeries.map φ (phiSer p hpR F i) = ((π p)⁻¹ : Kˣ).val • rho p (fK p F i) := by
  ext m
  rw [coeff_map, coeff_phiSer, φ_bcoef, map_smul, coeff_rho, smul_eq_mul, map_natCast, ← π_val]
  by_cases hm : m = 0
  · rw [hm, coeff_zero_eq_constantCoeff_apply, fK_const, mul_zero, mul_zero, mul_zero]
  · have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h => hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ,
      show (((π p)⁻¹ : Kˣ) : K) * ((((π p) : Kˣ) : K) ^ t * (((π p) : Kˣ) : K) * coeff m (fK p F i)) =
        (((π p) : Kˣ) : K) ^ t * coeff m (fK p F i) * ((((π p)⁻¹ : Kˣ) : K) * (((π p) : Kˣ) : K)) by ring,
      Units.inv_mul, mul_one]

theorem map_FpSer (i : Fin d) :
    MvPowerSeries.map φ (FpSer p F i) = ((π p)⁻¹ : Kˣ).val • rho p ((F.map φ).toPowerSeries i) := by
  classical
  ext m
  rw [coeff_map, coeff_FpSer, map_smul, coeff_rho, smul_eq_mul, ← π_val]
  show _ = _ * (_ * coeff m (MvPowerSeries.map φ (F.toPowerSeries i)))
  rw [coeff_map]
  by_cases hm : m = 0
  · rw [if_pos hm, map_zero, hm, coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero, map_zero]
    simp
  · rw [if_neg hm, map_mul, map_pow, map_natCast, ← π_val]
    have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h => hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ,
      show (((π p)⁻¹ : Kˣ) : K) * ((((π p) : Kˣ) : K) ^ t * (((π p) : Kˣ) : K) * φ (coeff m (F.toPowerSeries i))) =
        (((π p) : Kˣ) : K) ^ t * φ (coeff m (F.toPowerSeries i)) * ((((π p)⁻¹ : Kˣ) : K) * (((π p) : Kˣ) : K)) by ring,
      Units.inv_mul, mul_one]

include hpR in
theorem map_injective : Function.Injective (MvPowerSeries.map (σ := Fin d ⊕ Fin d) φ) := by
  intro f g h
  ext m
  apply φ_injective p hpR
  rw [← coeff_map, ← coeff_map, h]

theorem hasSubst_FpK : HasSubst fun j => ((π p)⁻¹ : Kˣ).val • rho p ((F.map φ).toPowerSeries j) :=
  hasSubst_of_constantCoeff_zero fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, map_smul, coeff_rho, coeff_zero_eq_constantCoeff_apply,
      (F.map φ).constantCoeff_eq_zero, mul_zero, smul_zero]

theorem phiSer_add (i : Fin d) :
    subst (FpSer p F) (phiSer p hpR F i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (phiSer p hpR F i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (phiSer p hpR F i) := by
  classical
  apply map_injective p hpR
  have hFp0 : ∀ j, constantCoeff (FpSer p F j) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_FpSer, if_pos rfl]
  have hFpS := hasSubst_of_constantCoeff_zero hFp0
  have hinl : HasSubst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have hinr : HasSubst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
  have hinlK : HasSubst (inlX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K) := hasSubst_of_constantCoeff_zero constantCoeff_inlX
  have hinrK : HasSubst (inrX : Fin d → MvPowerSeries (Fin d ⊕ Fin d) K) := hasSubst_of_constantCoeff_zero constantCoeff_inrX
  rw [map_add, MvPowerSeries.map_subst hFpS, MvPowerSeries.map_subst hinl, MvPowerSeries.map_subst hinr, map_phiSer]
  simp only [map_FpSer, MvPowerSeries.map_X]
  set u : K := ((π p)⁻¹ : Kˣ).val with hu
  set FK := F.map φ with hFK
  have hpu : (p : K) * u = 1 := by rw [hu, ← π_val, Units.mul_inv]

  have hL : subst (fun j => u • rho p (FK.toPowerSeries j)) (u • rho p (fK p F i)) = u • rho p (subst FK.toPowerSeries (fK p F i)) := by
    rw [subst_smul (hasSubst_FpK p F), ← subst_smul_family p (hasSubst_FpK p F)]
    have hfam : (fun s => (p : K) • (u • rho p (FK.toPowerSeries s))) = fun s => rho p (FK.toPowerSeries s) := by
      funext s; rw [smul_smul, hpu, one_smul]
    rw [hfam, rho_subst p FK.hasSubst_toPowerSeries]
  have hinlK' : HasSubst (fun t => (X (Sum.inl t) : MvPowerSeries (Fin d ⊕ Fin d) K)) :=
    hasSubst_of_constantCoeff_zero (fun t => constantCoeff_X _)
  have hinrK' : HasSubst (fun t => (X (Sum.inr t) : MvPowerSeries (Fin d ⊕ Fin d) K)) :=
    hasSubst_of_constantCoeff_zero (fun t => constantCoeff_X _)
  rw [hL, fK_add, map_add, rho_subst p hinlK, rho_subst p hinrK, smul_add]
  simp only [inlX, inrX, rho_X]
  rw [subst_smul_family p hinlK', subst_smul_family p hinrK', subst_smul hinlK', subst_smul hinrK']

end Descent

section MainSec

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]

include hpR in
theorem main :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),
      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧
      (∀ i, (Fp i).constantCoeff = 0) ∧
      (∀ i, (φ i).constantCoeff = 0) ∧
      MvFormalGroup.linearPart φ = 1 ∧
      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧
      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) := by
  classical
  refine ⟨FpSer p F, phiSer p hpR F, ?_, ?_, ?_, ?_, ?_, fun i => phiSer_add p hpR F i⟩
  · intro i m hm
    show coeff m (FpSer p F i) * _ = _ * coeff m (F.toPowerSeries i)
    rw [coeff_FpSer, if_neg hm]
    have h1 : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 (fun h => hm ((Finsupp.degree_eq_zero_iff m).1 h))
    obtain ⟨t, ht⟩ : ∃ t, m.degree = t + 1 := ⟨m.degree - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, pow_succ]
    ring
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_FpSer, if_pos rfl]
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_phiSer, bcoef, dif_pos rfl]
  · ext i j
    rw [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.one_apply]
    show coeff (Finsupp.single j 1) (phiSer p hpR F i) = _
    rw [coeff_phiSer]
    apply φ_injective p hpR
    rw [φ_bcoef, Finsupp.degree_single, Nat.sub_self, pow_zero, one_mul,
      (fK_lin p F i) _ (by rw [Finsupp.degree_single]), coeff_X]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (fun h => hij (Finsupp.single_left_injective one_ne_zero h).symm), if_neg hij, map_zero]
  · intro N i
    refine Filter.eventually_cofinite.2 ((lowDeg (Fin d) (2 * N + 1)).finite_toSet.subset fun m hm => ?_)
    rw [Finset.mem_coe, mem_lowDeg]
    by_contra h
    exact hm (bcoef_mem p hpR F i m N (by omega))

end MainSec

end S17LE
p2m_reactivate "P2MW.S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete.S17LE"

set_option autoImplicit false

open MvPowerSeries

universe u

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm] :
    ∃ (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (φ : Fin d → MvPowerSeries (Fin d) 𝓞),

      (∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
        (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m) ∧

      (∀ i, (Fp i).constantCoeff = 0) ∧

      (∀ i, (φ i).constantCoeff = 0) ∧

      MvFormalGroup.linearPart φ = 1 ∧

      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧

      (∀ i, subst Fp (φ i) =
        subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
          subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :=
  S17LE.main p hp F

end S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete
end P2MW
export P2MW.S_MvFormalGroup_exists_rescaledLog_of_isAdicComplete (solution)
