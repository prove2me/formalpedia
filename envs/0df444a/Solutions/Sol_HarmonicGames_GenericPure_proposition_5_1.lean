-- Prove2me | solution 1 for HarmonicGames.GenericPure.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:04:52.384317+00:00
-- url     : https://prove2.me/submissions/f84cddad-8723-492d-b9a4-8265f4f48a33

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HarmonicGames_GenericPure_Games

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P74955fb9

open HarmonicGames.Decomposition MeasureTheory
open scoped InnerProductSpace

section Pinv
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

lemma sub_proj_mem_ker (L : V →ₗ[ℝ] W) (x : V) :
    x - (LinearMap.ker L)ᗮ.starProjection x ∈ LinearMap.ker L := by
  have := (LinearMap.ker L)ᗮ.sub_starProjection_mem_orthogonal x
  rwa [Submodule.orthogonal_orthogonal] at this

lemma map_proj (L : V →ₗ[ℝ] W) (x : V) :
    L ((LinearMap.ker L)ᗮ.starProjection x) = L x := by
  have h1 := sub_proj_mem_ker L x
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1.symm

lemma pinv_apply_self (L : V →ₗ[ℝ] W) (x : V) :
    pinv L (L x) = (LinearMap.ker L)ᗮ.starProjection x := by
  set K := (LinearMap.ker L)ᗮ with hK
  set f := L ∘ₗ K.subtype with hf
  set y : K := K.orthogonalProjectionOnto x with hy
  have hk : L x = f y := by
    rw [← map_proj L x, Submodule.starProjection_apply]; rfl
  have hr : (LinearMap.range f).orthogonalProjectionOnto (f y) =
      ⟨f y, LinearMap.mem_range_self f y⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f y, LinearMap.mem_range_self f y⟩
  have he : (LinearEquiv.ofInjective f (pinv_restrict_injective L)).symm
      ⟨f y, LinearMap.mem_range_self f y⟩ = y := by
    rw [LinearEquiv.symm_apply_eq]; ext; simp
  unfold pinv
  rw [hk]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hr]
  have := congrArg K.subtype he
  exact this.trans (by rw [Submodule.starProjection_apply]; rfl)

lemma pinv_idem (L : V →ₗ[ℝ] W) (x : V) :
    pinv L (L (pinv L (L x))) = pinv L (L x) := by
  rw [pinv_apply_self, pinv_apply_self]
  exact (Submodule.starProjection_eq_self_iff).2 (Submodule.starProjection_apply_mem _ _)

lemma map_pinv (L : V →ₗ[ℝ] W) (x : V) : L (pinv L (L x)) = L x := by
  rw [pinv_apply_self, map_proj]

end Pinv

section Graph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma C1_sum_apply {α : Type*} (s : Finset α) (f : α → C1 G) (a b : V) :
    (∑ m ∈ s, f m) a b = ∑ m ∈ s, f m a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, C1.add_apply, ih]

lemma inner_delta0 (φ : C0 V) (X : C1 G) :
    ⟪delta0 G φ, X⟫_ℝ = -∑ a, φ a * ∑ b, X a b := by
  have h0 : ⟪delta0 G φ, X⟫_ℝ = innerC1 G (delta0 G φ) X := rfl
  have hterm : ∀ a b, (if G.Adj a b then delta0 G φ a b * X a b else 0) =
      (φ b - φ a) * X a b := by
    intro a b
    by_cases h : G.Adj a b
    · rw [if_pos h]
      show ((if G.Adj a b then (1:ℝ) else 0) * (φ b - φ a)) * X a b = _
      rw [if_pos h, one_mul]
    · rw [if_neg h, C1.eq_zero_of_not_adj G X h, mul_zero]
  have hanti : ∀ a b, X b a = - X a b := by
    intro a b
    by_cases h : G.Adj a b
    · exact C1.antisymm G X h
    · rw [C1.eq_zero_of_not_adj G X h, C1.eq_zero_of_not_adj G X (fun h' => h h'.symm), neg_zero]
  rw [h0, innerC1]
  simp_rw [hterm, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ a, ∑ b, φ b * X a b = -∑ a, ∑ b, φ a * X a b := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hanti a b]; ring
  rw [h1]
  simp_rw [Finset.mul_sum]
  ring

lemma mem_ker_adjoint_iff (X : C1 G) :
    X ∈ LinearMap.ker (LinearMap.adjoint (delta0 G)) ↔ ∀ a, ∑ b, X a b = 0 := by
  constructor
  · intro hX a
    classical
    have := LinearMap.adjoint_inner_right (delta0 G) (EuclideanSpace.single a (1:ℝ)) X
    rw [LinearMap.mem_ker.1 hX, inner_zero_right, inner_delta0] at this
    simpa [PiLp.single_apply] using this.symm
  · intro h
    rw [LinearMap.mem_ker]
    refine ext_inner_left ℝ fun φ => ?_
    rw [LinearMap.adjoint_inner_right, inner_delta0, inner_zero_right]
    simp [h]

end Graph

section Games
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

lemma Dop_apply (u : Games E) (a b : ∀ k, E k) :
    (Dop E u) a b = ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (u m b - u m a) := by
  show (∑ m, Dm E m (u m)) a b = _
  rw [C1_sum_apply]
  rfl

lemma div_of_mem (v : Games E) (hv : v ∈ HarmonicGames.GenericPure.harmonicGames E)
    (a : ∀ k, E k) :
    ∑ b, ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (v m b - v m a) = 0 := by
  obtain ⟨h, hh, n, hn, rfl⟩ := Submodule.mem_sup.1 hv
  have hD : Dop E (h + n) = Dop E h := by
    rw [map_add, LinearMap.mem_ker.1 hn, add_zero]
  have hk : Dop E h ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E))) :=
    Submodule.mem_comap.1 hh.2
  rw [← hD] at hk
  have := (mem_ker_adjoint_iff _ _).1 hk a
  simpa only [Dop_apply] using this

lemma eq_of_nash (v : Games E) (hv : v ∈ HarmonicGames.GenericPure.harmonicGames E)
    (p : ∀ k, E k) (hp : AGT.IsPureNash (HarmonicGames.GenericPure.payoff E v) p) :
    ∀ m b, MComparable E m p b → v m b = v m p := by
  have hd := div_of_mem E v hv p
  have hnp : ∀ b m, (if MComparable E m p b then (1:ℝ) else 0) * (v m b - v m p) ≤ 0 := by
    intro b m
    split_ifs with hc
    · rw [one_mul, sub_nonpos]
      have hb : b = Function.update p m (b m) := by
        funext k
        by_cases hk : k = m
        · subst hk; simp
        · rw [Function.update_of_ne hk]; exact (hc.2 k hk).symm
      have h1 : v m (Function.update p m (b m)) ≤ v m p := hp m (b m)
      rw [← hb] at h1
      exact h1
    · rw [zero_mul]
  intro m b hc
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun b _ => Finset.sum_nonpos fun m _ => hnp b m)).1 hd b (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun m _ => hnp b m)).1 h1 m (Finset.mem_univ _)
  rw [if_pos hc, one_mul, sub_eq_zero] at h2
  exact h2

/-- The subspace of harmonic games all of whose deviations at `p` are payoff-neutral. -/
def Sp (p : ∀ k, E k) : Submodule ℝ (HarmonicGames.GenericPure.harmonicGames E) where
  carrier := {v | ∀ m b, MComparable E m p b → (v : Games E) m b = (v : Games E) m p}
  add_mem' := by
    intro v w hv hw m b hc
    simp [hv m b hc, hw m b hc]
  zero_mem' := by
    intro m b hc
    simp
  smul_mem' := by
    intro c v hv m b hc
    simp [hv m b hc]

lemma sum_mcomp (m : ι) (f : (∀ k, E k) → ℝ) (a : ∀ k, E k) :
    ∑ b, (if MComparable E m a b then (1:ℝ) else 0) * (f b - f a) =
      ∑ c : E m, (f (Function.update a m c) - f a) := by
  have himg : ∑ c : E m, (f (Function.update a m c) - f a) =
      ∑ b ∈ Finset.univ.image (fun c => Function.update a m c), (f b - f a) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Function.update_injective a m hxy
  rw [himg, ← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image fun c => Function.update a m c))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hb
    split_ifs with hc
    · ring
    · have : Function.update a m c = a := by
        by_contra hne'
        exact hc ⟨fun e => hne' e.symm, fun k hk => (Function.update_of_ne hk c a).symm⟩
      rw [this]; ring
  · intro b _ hb
    split_ifs with hc
    · exfalso
      apply hb
      refine Finset.mem_image.2 ⟨b m, Finset.mem_univ _, ?_⟩
      funext k
      by_cases hk : k = m
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hc.2 k hk
    · ring

lemma PiOp_apply (u : Games E) (m : ι) : (PiOp E u) m = Pim E m (u m) := rfl

lemma Dop_PiOp (u : Games E) : Dop E (PiOp E u) = Dop E u := by
  show ∑ m, Dm E m ((PiOp E u) m) = ∑ m, Dm E m (u m)
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [PiOp_apply]
  exact map_pinv _ _

lemma PiOp_idem (u : Games E) : PiOp E (PiOp E u) = PiOp E u := by
  ext m b
  rw [PiOp_apply, PiOp_apply]
  show pinv (Dm E m) (Dm E m (pinv (Dm E m) (Dm E m (u m)))) b = pinv (Dm E m) (Dm E m (u m)) b
  rw [pinv_idem]

lemma mem_of_div (u : Games E)
    (hu : ∀ a, ∑ b, ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (u m b - u m a) = 0) :
    u ∈ HarmonicGames.GenericPure.harmonicGames E := by
  have hD : Dop E u ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E))) := by
    rw [mem_ker_adjoint_iff]
    intro a
    simpa only [Dop_apply] using hu a
  have hH : PiOp E u ∈ HarmonicGames.GenericPure.harmonicSubspace E := by
    refine ⟨?_, ?_⟩
    · show LinearMap.id (PiOp E u) = PiOp E (PiOp E u)
      rw [PiOp_idem]; rfl
    · show Dop E (PiOp E u) ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E)))
      rw [Dop_PiOp]; exact hD
  have hN : u - PiOp E u ∈ nonstrategicSubspace E := by
    rw [nonstrategicSubspace, LinearMap.mem_ker, map_sub, Dop_PiOp, sub_self]
  exact Submodule.mem_sup.2 ⟨_, hH, _, hN, add_sub_cancel _ _⟩

lemma Sp_ne_top (h2 : ∃ m₁ m₂ : ι, m₁ ≠ m₂ ∧ 2 ≤ Fintype.card (E m₁) ∧ 2 ≤ Fintype.card (E m₂))
    (p : ∀ k, E k) : Sp E p ≠ ⊤ := by
  obtain ⟨m₁, m₂, hne, hc1, hc2⟩ := h2
  obtain ⟨a₁, ha₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (p m₁)
  obtain ⟨a₂, ha₂⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (p m₂)
  set n₁ : ℝ := (Fintype.card (E m₁) : ℝ) with hn₁
  set n₂ : ℝ := (Fintype.card (E m₂) : ℝ) with hn₂
  have hn₂pos : 0 < n₂ := by rw [hn₂]; exact_mod_cast (by omega : 0 < Fintype.card (E m₂))
  let g : E m₁ → ℝ := fun c => (if c = p m₁ then 1 else 0) - (if c = a₁ then 1 else 0)
  let h : E m₂ → ℝ := fun c => (if c = p m₂ then 1 else 0) - (if c = a₂ then 1 else 0)
  have hg : ∑ c, g c = 0 := by simp [g, Finset.sum_sub_distrib]
  have hh : ∑ c, h c = 0 := by simp [h, Finset.sum_sub_distrib]
  let U : ι → (∀ k, E k) → ℝ := fun m b =>
    if m = m₁ then n₂ * (g (b m₁) * h (b m₂))
    else if m = m₂ then -(n₁ * (g (b m₁) * h (b m₂))) else 0
  let u : Games E := WithLp.toLp 2 (fun m => WithLp.toLp 2 (U m))
  have hu : ∀ m b, u m b = U m b := fun _ _ => rfl
  have hdiv : ∀ a, ∑ b, ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (u m b - u m a) = 0 := by
    intro a
    rw [Finset.sum_comm]
    simp_rw [sum_mcomp E _ (fun b => u _ b) a, hu]
    rw [Fintype.sum_eq_add m₁ m₂ hne]
    · have e1 : ∀ c, U m₁ (Function.update a m₁ c) = n₂ * h (a m₂) * g c := by
        intro c
        simp only [U, if_pos rfl, Function.update_self, Function.update_of_ne hne.symm]
        ring
      have e2 : ∀ c, U m₂ (Function.update a m₂ c) = -(n₁ * g (a m₁)) * h c := by
        intro c
        simp only [U, if_neg hne.symm, Function.update_self,
          Function.update_of_ne hne, ↓reduceIte]
        ring
      simp_rw [e1, e2]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hg, hh, Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
        nsmul_eq_mul, nsmul_eq_mul]
      simp only [U, if_neg hne.symm, ↓reduceIte]
      rw [← hn₁, ← hn₂]
      ring
    · intro m ⟨hm1, hm2⟩
      simp [U, hm1, hm2]
  have hmem := mem_of_div E u hdiv
  intro htop
  have hS : (⟨u, hmem⟩ : HarmonicGames.GenericPure.harmonicGames E) ∈ Sp E p := by
    rw [htop]; exact Submodule.mem_top
  have hmc : MComparable E m₁ p (Function.update p m₁ a₁) := by
    refine ⟨fun e => ha₁ ?_, fun k hk => (Function.update_of_ne hk a₁ p).symm⟩
    have := congrFun e m₁
    rw [Function.update_self] at this
    exact this.symm
  have key := hS m₁ _ hmc
  change U m₁ (Function.update p m₁ a₁) = U m₁ p at key
  simp [U, g, h, Function.update_of_ne hne.symm, ha₁, ha₁.symm, ha₂.symm] at key
  try linarith

end Games

end P74955fb9

open HarmonicGames.GenericPure MeasureTheory in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (h2 : ∃ m₁ m₂ : ι, m₁ ≠ m₂ ∧ 2 ≤ Fintype.card (E m₁) ∧ 2 ≤ Fintype.card (E m₂))
    (μ : Measure (harmonicGames E)) [μ.IsAddHaarMeasure] :
    μ {v : harmonicGames E | ∃ p : ∀ m, E m, AGT.IsPureNash (payoff E (v : HarmonicGames.Decomposition.Games E)) p} = 0 := by
  have hsub : {v : harmonicGames E | ∃ p : ∀ m, E m,
      AGT.IsPureNash (payoff E (v : HarmonicGames.Decomposition.Games E)) p} ⊆
      ⋃ p : ∀ m, E m, ((P74955fb9.Sp E p : Submodule ℝ (harmonicGames E)) : Set (harmonicGames E)) := by
    rintro v ⟨p, hp⟩
    exact Set.mem_iUnion.2 ⟨p, P74955fb9.eq_of_nash E v.1 v.2 p hp⟩
  exact measure_mono_null hsub (measure_iUnion_null fun p =>
    Measure.addHaar_submodule μ _ (P74955fb9.Sp_ne_top E h2 p))
