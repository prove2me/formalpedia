-- Prove2me | solution 1 for Grunbaum2003.generic_projection_nonpolytope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T18:27:05.938142+00:00
-- url     : https://prove2.me/submissions/66664635-013c-4286-b60d-6e22df115aba

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Standard dot-product linear functional on `Fin d → ℝ` associated to a vector `a`. -/
def dotMap {d : ℕ} (a : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i : Fin d, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)

theorem dotMap_apply {d : ℕ} (a x : Fin d → ℝ) :
    dotMap a x = ∑ i : Fin d, a i * x i := rfl

@[simp]
theorem dotMap_zero {d : ℕ} : dotMap (0 : Fin d → ℝ) = 0 := by
  ext x; simp [dotMap]

theorem dotMap_add {d : ℕ} (a b : Fin d → ℝ) :
    dotMap (a + b) = dotMap a + dotMap b := by
  ext x; simp [dotMap, add_mul, Finset.sum_add_distrib]

theorem dotMap_smul {d : ℕ} (c : ℝ) (a : Fin d → ℝ) :
    dotMap (c • a) = c • dotMap a := by
  apply LinearMap.ext
  intro x
  change ∑ i : Fin d, (c • a) i * x i = c * ∑ i : Fin d, a i * x i
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => by simp [mul_assoc])

theorem dotMap_self_pos {d : ℕ} {u : Fin d → ℝ} (hu : u ≠ 0) :
    0 < dotMap u u := by
  have hex : ∃ i : Fin d, u i ≠ 0 := Function.ne_iff.mp hu
  obtain ⟨i₀, hi₀⟩ := hex
  have hpos : 0 < u i₀ * u i₀ := mul_self_pos.mpr hi₀
  have hle : u i₀ * u i₀ ≤ ∑ i : Fin d, u i * u i :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i₀)
  exact lt_of_lt_of_le hpos hle

/-- Subset of `S` maximizing the linear functional `dotMap a`. -/
def maxSet {d : ℕ} (S : Set (Fin d → ℝ)) (a : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x ∈ S | ∀ y ∈ S, dotMap a y ≤ dotMap a x}

theorem maxSet_subset {d : ℕ} (S : Set (Fin d → ℝ)) (a : Fin d → ℝ) :
    maxSet S a ⊆ S := fun _ hx => hx.1

theorem maxSet_zero {d : ℕ} (S : Set (Fin d → ℝ)) :
    maxSet S 0 = S := by
  ext x; simp [maxSet]

theorem maxSet_smul_pos {d : ℕ} (S : Set (Fin d → ℝ)) (a : Fin d → ℝ) {c : ℝ} (hc : 0 < c) :
    maxSet S (c • a) = maxSet S a := by
  ext x
  simp [maxSet, dotMap_smul, mul_le_mul_iff_of_pos_left hc]

theorem maxSet_isCompact {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsCompact S) (a : Fin d → ℝ) :
    IsCompact (maxSet S a) := by
  have hclosed : IsClosed {x : Fin d → ℝ | ∀ y ∈ S, dotMap a y ≤ dotMap a x} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter (fun y => ?_)
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun _ =>
      isClosed_le continuous_const (dotMap a).continuous_of_finiteDimensional)
  exact hS.inter_right hclosed

theorem maxSet_nonempty {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsCompact S) (hSne : S.Nonempty)
    (a : Fin d → ℝ) : (maxSet S a).Nonempty :=
  hS.exists_isMaxOn hSne (dotMap a).continuous_of_finiteDimensional.continuousOn

/-- Positive combination lemma: if `maxSet K b ⊆ maxSet K a` and `maxSet K b` is nonempty,
then for any `c₀ ≥ 0` and `c₁ > 0`, `maxSet K (c₀ • a + c₁ • b) = maxSet K b`. -/
theorem maxSet_pos_add {d : ℕ} {K : Set (Fin d → ℝ)} {a b : Fin d → ℝ}
    (hsub : maxSet K b ⊆ maxSet K a) (hne : (maxSet K b).Nonempty)
    {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 < c₁) :
    maxSet K (c₀ • a + c₁ • b) = maxSet K b := by
  obtain ⟨p, hp⟩ := hne
  have hpa : p ∈ maxSet K a := hsub hp
  ext x
  simp only [maxSet, Set.mem_setOf_eq, dotMap_add, dotMap_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hxK, hmax⟩
    refine ⟨hxK, fun y hyK => ?_⟩
    have hxp := hmax p hp.1
    have hax := hpa.2 x hxK
    have hyb := hp.2 y hyK
    nlinarith
  · rintro ⟨hxK, hxb⟩
    have hxa : x ∈ maxSet K a := hsub ⟨hxK, hxb⟩
    refine ⟨hxK, fun y hyK => ?_⟩
    have hya := hxa.2 y hyK
    have hyb := hxb y hyK
    nlinarith

/-- Extending a surjective linear map onto `Fin 2 → ℝ` to a surjective linear map onto
`Fin j → ℝ` (`2 ≤ j < d`), so that polytopality of `j`-dimensional projections implies
polytopality of `2`-dimensional projections. -/
theorem aux_proj_two_of_proj_j {d j : ℕ} (hj2 : 2 ≤ j) (hjd : j < d)
    (K : Set (Fin d → ℝ))
    (hproj : ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
      ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W)
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (hLsurj : Function.Surjective L) :
    ∃ W : Set (Fin 2 → ℝ), W.Finite ∧ L '' K = convexHull ℝ W := by
  obtain ⟨v0, hv0⟩ := hLsurj (Pi.single 0 1)
  obtain ⟨v1, hv1⟩ := hLsurj (Pi.single 1 1)
  have hker_dim : Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ (Fin (d - 2) → ℝ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have hr : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hLsurj
    rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let E : LinearMap.ker L ≃ₗ[ℝ] (Fin (d - 2) → ℝ) := LinearEquiv.ofFinrankEq _ _ hker_dim
  let π : (Fin d → ℝ) →ₗ[ℝ] LinearMap.ker L :=
    { toFun := fun x => ⟨x - L x 0 • v0 - L x 1 • v1, by
        rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, hv0, hv1]
        ext i
        fin_cases i <;> simp⟩
      map_add' := fun x y => by
        ext i
        simp only [Submodule.coe_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add,
          smul_eq_mul]
        ring
      map_smul' := fun c x => by
        ext i
        simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, Pi.sub_apply, map_smul,
          RingHom.id_apply, smul_eq_mul]
        ring }
  let coord : Fin j → ((Fin d → ℝ) →ₗ[ℝ] ℝ) := fun i =>
    if hi0 : i.val = 0 then
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp L
    else if hi1 : i.val = 1 then
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp L
    else
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d - 2) => ℝ)
        ⟨i.val - 2, by omega⟩).comp (E.toLinearMap.comp π)
  let L_ext : (Fin d → ℝ) →ₗ[ℝ] (Fin j → ℝ) := LinearMap.pi coord
  have h_ext_surj : Function.Surjective L_ext := by
    intro y
    let kvec : Fin (d - 2) → ℝ := fun m =>
      if hm : m.val + 2 < j then y ⟨m.val + 2, hm⟩ else 0
    let w : LinearMap.ker L := E.symm kvec
    have hw_ker : L (w : Fin d → ℝ) = 0 := w.2
    let x : Fin d → ℝ := y ⟨0, by omega⟩ • v0 + y ⟨1, by omega⟩ • v1 + (w : Fin d → ℝ)
    have hLx0 : L x 0 = y ⟨0, by omega⟩ := by
      simp [x, map_add, map_smul, hv0, hv1, hw_ker]
    have hLx1 : L x 1 = y ⟨1, by omega⟩ := by
      simp [x, map_add, map_smul, hv0, hv1, hw_ker]
    have hπx : π x = w := by
      ext i
      simp only [π, LinearMap.coe_mk, AddHom.coe_mk, hLx0, hLx1, x, Pi.add_apply, Pi.sub_apply]
      ring
    use x
    ext i
    simp only [L_ext, LinearMap.pi_apply, coord]
    split_ifs with hi0 hi1
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      simp [hi, hLx0]
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      simp [hi, hLx1]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hπx, w,
        LinearEquiv.apply_symm_apply, LinearMap.proj_apply, kvec]
      have hm : (i.val - 2) + 2 < j := by omega
      rw [dif_pos hm]
      congr 1
      exact Fin.ext (by simp; omega)
  obtain ⟨Wj, hWjfin, hWj⟩ := hproj L_ext.toAffineMap h_ext_surj
  let P2 : (Fin j → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi ![
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) ⟨0, by omega⟩,
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) ⟨1, by omega⟩
    ]
  have hPL : P2.comp L_ext = L := by
    ext x i
    fin_cases i <;> simp [P2, L_ext, coord]
  refine ⟨P2 '' Wj, hWjfin.image P2, ?_⟩
  rw [← P2.image_convexHull Wj, ← hWj, Set.image_image]
  refine Set.image_congr (fun x _ => ?_)
  exact congrFun (congrArg DFunLike.coe hPL.symm) x

/-- Claim 1 (Directional stabilization): if every surjective linear projection `ℝ^d → ℝ^2` sends
`K` to a finite convex hull, then for any `a, u : Fin d → ℝ`, there exists `t > 0` such that
`maxSet K (a + t • u) = maxSet (maxSet K a) u`. -/
theorem aux_directional_stabilization {d : ℕ} {K : Set (Fin d → ℝ)}
    (hcompact : IsCompact K) (hKne : K.Nonempty)
    (hproj2 : ∀ L : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective L →
      ∃ W : Set (Fin 2 → ℝ), W.Finite ∧ L '' K = convexHull ℝ W)
    (a u : Fin d → ℝ) :
    ∃ t : ℝ, 0 < t ∧ maxSet K (a + t • u) = maxSet (maxSet K a) u := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi ![dotMap a, dotMap u]
  by_cases hsurj : Function.Surjective L
  · obtain ⟨W0, hW0fin, hLW0⟩ := hproj2 L hsurj
    have hW0sub : W0 ⊆ L '' K := hLW0 ▸ subset_convexHull ℝ W0
    have hFa_comp : IsCompact (maxSet K a) := maxSet_isCompact hcompact a
    have hFa_ne : (maxSet K a).Nonempty := maxSet_nonempty hcompact hKne a
    obtain ⟨xstar, hxstar⟩ := maxSet_nonempty hFa_comp hFa_ne u
    let M0 : ℝ := dotMap a xstar
    let Mu : ℝ := dotMap u xstar
    let F : Finset (Fin 2 → ℝ) := hW0fin.toFinset
    let C : ℝ := 1 + ∑ w ∈ F, if w 0 < M0 then max 0 (w 1 - Mu) / (M0 - w 0) else 0
    have hC_ge1 : 1 ≤ C := by
      dsimp [C]
      suffices 0 ≤ ∑ w ∈ F, (if w 0 < M0 then max 0 (w 1 - Mu) / (M0 - w 0) else 0) by linarith
      refine Finset.sum_nonneg (fun w _ => ?_)
      split_ifs with hw
      · exact div_nonneg (le_max_left 0 _) (by linarith)
      · exact le_rfl
    have hC_pos : 0 < C := by linarith
    have hW0_ineq : W0 ⊆ {w : Fin 2 → ℝ | C * w 0 + w 1 ≤ C * M0 + Mu} := by
      intro w hwW0
      obtain ⟨x, hxK, hLx⟩ := hW0sub hwW0
      have hw0_ax : w 0 = dotMap a x := by
        have : L x 0 = w 0 := congrFun hLx 0
        exact this.symm
      have hw1_ux : w 1 = dotMap u x := by
        have : L x 1 = w 1 := congrFun hLx 1
        exact this.symm
      have hw0_le : w 0 ≤ M0 := by
        rw [hw0_ax]
        exact hxstar.1.2 x hxK
      rcases lt_or_eq_of_le hw0_le with hw0_lt | hw0_eq
      · have hwF : w ∈ F := hW0fin.mem_toFinset.mpr hwW0
        have hterm_le : max 0 (w 1 - Mu) / (M0 - w 0) ≤
            ∑ w' ∈ F, (if w' 0 < M0 then max 0 (w' 1 - Mu) / (M0 - w' 0) else 0) := by
          have h1 := Finset.single_le_sum (f := fun w' : Fin 2 → ℝ =>
            if w' 0 < M0 then max 0 (w' 1 - Mu) / (M0 - w' 0) else 0)
            (fun w' _ => by
              split_ifs with h
              · exact div_nonneg (le_max_left 0 _) (by linarith)
              · exact le_rfl) hwF
          simpa [hw0_lt] using h1
        have hdiv_le : max 0 (w 1 - Mu) / (M0 - w 0) ≤ C := by dsimp [C]; linarith
        have hmul : max 0 (w 1 - Mu) ≤ C * (M0 - w 0) :=
          (div_le_iff₀ (by linarith)).mp hdiv_le
        have hle2 : w 1 - Mu ≤ max 0 (w 1 - Mu) := le_max_right 0 _
        simp only [Set.mem_setOf_eq]
        linarith
      · have hx_in_Fa : x ∈ maxSet K a := by
          refine ⟨hxK, fun y hyK => ?_⟩
          have h2 : dotMap a y ≤ M0 := hxstar.1.2 y hyK
          linarith
        have hw1_le : w 1 ≤ Mu := by
          rw [hw1_ux]
          exact hxstar.2 x hx_in_Fa
        simp only [Set.mem_setOf_eq]
        rw [hw0_eq]
        linarith
    have hH_conv : Convex ℝ {w : Fin 2 → ℝ | C * w 0 + w 1 ≤ C * M0 + Mu} := by
      intro w1 hw1 w2 hw2 α β hα hβ hαβ
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hw1 hw2 ⊢
      have h1 := mul_le_mul_of_nonneg_left hw1 hα
      have h2 := mul_le_mul_of_nonneg_left hw2 hβ
      calc C * (α * w1 0 + β * w2 0) + (α * w1 1 + β * w2 1)
          = α * (C * w1 0 + w1 1) + β * (C * w2 0 + w2 1) := by ring
        _ ≤ α * (C * M0 + Mu) + β * (C * M0 + Mu) := add_le_add h1 h2
        _ = (α + β) * (C * M0 + Mu) := by ring
        _ = C * M0 + Mu := by rw [hαβ, one_mul]
    have hK_ineq : ∀ x ∈ K, C * dotMap a x + dotMap u x ≤ C * M0 + Mu := by
      intro x hxK
      have hLx : L x ∈ convexHull ℝ W0 := hLW0 ▸ ⟨x, hxK, rfl⟩
      have h := convexHull_min hW0_ineq hH_conv hLx
      exact h
    refine ⟨1 / (C + 1), by positivity, ?_⟩
    ext x
    simp only [maxSet, Set.mem_setOf_eq, dotMap_add, dotMap_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hxK, hmax⟩
      have h1 : dotMap a xstar + 1 / (C + 1) * dotMap u xstar ≤
          dotMap a x + 1 / (C + 1) * dotMap u x := hmax xstar hxstar.1.1
      have h2 : dotMap a x ≤ M0 := hxstar.1.2 x hxK
      have h3 : C * dotMap a x + dotMap u x ≤ C * M0 + Mu := hK_ineq x hxK
      have hM0 : dotMap a xstar = M0 := rfl
      have hMu : dotMap u xstar = Mu := rfl
      have ht : 0 < 1 / (C + 1) := by positivity
      have hCt : (1 / (C + 1)) * (C + 1) = 1 := one_div_mul_cancel (by linarith)
      have ha_eq : dotMap a x = M0 := by nlinarith
      have hu_eq : dotMap u x = Mu := by nlinarith
      refine ⟨⟨hxK, fun y hyK => ?_⟩, fun y hyFa => ?_⟩
      · have hy : dotMap a y ≤ M0 := hxstar.1.2 y hyK
        linarith
      · have hy : dotMap u y ≤ Mu := hxstar.2 y hyFa
        linarith
    · rintro ⟨⟨hxK, hxa⟩, hxu⟩
      have ha_eq : dotMap a x = M0 := le_antisymm (hxstar.1.2 x hxK) (hxa xstar hxstar.1.1)
      have hu_eq : dotMap u x = Mu := le_antisymm (hxstar.2 x ⟨hxK, hxa⟩) (hxu xstar hxstar.1)
      refine ⟨hxK, fun y hyK => ?_⟩
      have hy1 : dotMap a y ≤ M0 := hxstar.1.2 y hyK
      have hy2 : C * dotMap a y + dotMap u y ≤ C * M0 + Mu := hK_ineq y hyK
      have ht : 0 < 1 / (C + 1) := by positivity
      have hCt : (1 / (C + 1)) * (C + 1) = 1 := one_div_mul_cancel (by linarith)
      nlinarith
  · by_cases ha0 : a = 0
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [ha0, zero_add, one_smul, maxSet_zero]
    · have hpos_a : 0 < dotMap a a := dotMap_self_pos ha0
      let v0 : Fin d → ℝ := (dotMap a a)⁻¹ • a
      have hav0 : dotMap a v0 = 1 := by
        dsimp [v0]
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hpos_a)]
      have hdep : ∀ x : Fin d → ℝ, dotMap u x = dotMap u v0 * dotMap a x := by
        intro x
        by_contra hne
        have hnz : dotMap u (x - dotMap a x • v0) ≠ 0 := by
          rw [map_sub, map_smul, smul_eq_mul, mul_comm]
          exact sub_ne_zero.mpr hne
        let v1 : Fin d → ℝ := (dotMap u (x - dotMap a x • v0))⁻¹ • (x - dotMap a x • v0)
        have ha_sub : dotMap a (x - dotMap a x • v0) = 0 := by
          rw [map_sub, map_smul, hav0, smul_eq_mul, mul_one, sub_self]
        have hav1 : dotMap a v1 = 0 := by
          dsimp [v1]
          rw [map_smul, ha_sub, smul_zero]
        have huv1 : dotMap u v1 = 1 := by
          dsimp [v1]
          rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hnz]
        apply hsurj
        intro y
        use y 0 • v0 + (y 1 - y 0 * dotMap u v0) • v1
        ext i
        fin_cases i
        · simp [L, map_add, map_smul, hav0, hav1]
        · simp [L, map_add, map_smul, huv1]
      let c : ℝ := dotMap u v0
      let t : ℝ := 1 / (|c| + 1)
      have ht : 0 < t := by positivity
      have h1tc : 0 < 1 + t * c := by
        have hle : -|c| ≤ c := neg_abs_le c
        have h2 : t * (|c| + 1) = 1 := one_div_mul_cancel (by positivity)
        nlinarith [abs_nonneg c]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [maxSet, Set.mem_setOf_eq, dotMap_add, dotMap_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      constructor
      · rintro ⟨hxK, hmax⟩
        have hxa : ∀ y ∈ K, dotMap a y ≤ dotMap a x := by
          intro y hyK
          have hmy := hmax y hyK
          rw [hdep y, hdep x] at hmy
          change dotMap a y + t * (c * dotMap a y) ≤ dotMap a x + t * (c * dotMap a x) at hmy
          nlinarith
        refine ⟨⟨hxK, hxa⟩, fun y ⟨hyK, hya⟩ => ?_⟩
        have h_eq : dotMap a y = dotMap a x := le_antisymm (hxa y hyK) (hya x hxK)
        rw [hdep y, hdep x, h_eq]
      · rintro ⟨⟨hxK, hxa⟩, _⟩
        refine ⟨hxK, fun y hyK => ?_⟩
        have hay := hxa y hyK
        rw [hdep y, hdep x]
        change dotMap a y + t * (c * dotMap a y) ≤ dotMap a x + t * (c * dotMap a x)
        nlinarith

/-- Positive lower bound for a positive function on a `Finset`. -/
theorem aux_exists_pos_le {α : Type*} (F : Finset α) (f : α → ℝ) (hf : ∀ x ∈ F, 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ F, r ≤ f x := by
  induction F using Finset.cons_induction with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | cons a s ha ih =>
    obtain ⟨r0, hr0, hle0⟩ := ih (fun x hx => hf x (Finset.mem_cons_of_mem hx))
    refine ⟨min (f a) r0, lt_min (hf a (Finset.mem_cons_self a s)) hr0, ?_⟩
    intro x hx
    rcases Finset.mem_cons.mp hx with rfl | hxs
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (hle0 x hxs)

/-- Inductive wedge lemma: for every subspace `W ≤ Fin d → ℝ` of `finrank = k` and every `a : Fin d → ℝ`,
there exist `r > 0` and a finite family `A` of subsets of `K` such that for all `w ∈ W` with
`‖w‖ ≤ r`, `maxSet K (a + w) ∈ A` and `maxSet K (a + w) ⊆ maxSet K a`. -/
theorem aux_finite_faces_wedge {d : ℕ} {K : Set (Fin d → ℝ)}
    (hcompact : IsCompact K) (hKne : K.Nonempty)
    (hproj2 : ∀ L : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective L →
      ∃ W : Set (Fin 2 → ℝ), W.Finite ∧ L '' K = convexHull ℝ W) :
    ∀ (k : ℕ) (W : Submodule ℝ (Fin d → ℝ)), Module.finrank ℝ W = k →
      ∀ a : Fin d → ℝ, ∃ (r : ℝ) (A : Set (Set (Fin d → ℝ))),
        0 < r ∧ A.Finite ∧ ∀ w ∈ W, ‖w‖ ≤ r →
          maxSet K (a + w) ∈ A ∧ maxSet K (a + w) ⊆ maxSet K a := by
  intro k
  induction k with
  | zero =>
    intro W hW a
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    refine ⟨1, {maxSet K a}, zero_lt_one, Set.finite_singleton _, ?_⟩
    intro w hw _
    rw [hbot, Submodule.mem_bot] at hw
    subst hw
    simp
  | succ k ih =>
    intro W hW a
    let SW : Set (Fin d → ℝ) := (W : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1
    have hSW_comp : IsCompact SW :=
      (isCompact_sphere (0 : Fin d → ℝ) 1).inter_left W.closed_of_finiteDimensional
    have hstep : ∀ u : Fin d → ℝ, ∃ (tu ru : ℝ) (Au : Set (Set (Fin d → ℝ))),
        u ∈ SW →
        0 < tu ∧ 0 < ru ∧ ru ≤ tu / 2 ∧ Au.Finite ∧
        ∀ w' : Fin d → ℝ, w' ∈ W → dotMap u w' = 0 → ‖w'‖ ≤ ru →
          maxSet K (a + tu • u + w') ∈ Au ∧
          maxSet K (a + tu • u + w') ⊆ maxSet K (a + tu • u) ∧
          maxSet K (a + tu • u) ⊆ maxSet K a := by
      intro u
      by_cases hu : u ∈ SW
      · rcases hu with ⟨huW, huS⟩
        have hu_norm : ‖u‖ = 1 := by simpa using huS
        have hu_ne : u ≠ 0 := by intro h0; simp [h0] at hu_norm
        obtain ⟨tu, htu, hmax_u⟩ := aux_directional_stabilization hcompact hKne hproj2 a u
        have hsub_u : maxSet K (a + tu • u) ⊆ maxSet K a := by
          rw [hmax_u]; exact maxSet_subset _ _
        let φ : W →ₗ[ℝ] ℝ := (dotMap u).comp W.subtype
        have hφ_ne : φ ≠ 0 := by
          intro h0
          have hpos := dotMap_self_pos hu_ne
          have : φ ⟨u, huW⟩ = 0 := by rw [h0]; rfl
          simp only [φ, LinearMap.comp_apply, Submodule.coe_subtype] at this
          linarith
        have hker_dim : Module.finrank ℝ (LinearMap.ker φ) = k := by
          have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ_ne
          omega
        let Wu : Submodule ℝ (Fin d → ℝ) := (LinearMap.ker φ).map W.subtype
        have hWu_dim : Module.finrank ℝ Wu = k := by
          dsimp [Wu]
          rw [Submodule.finrank_map_subtype_eq]
          exact hker_dim
        obtain ⟨ru0, Au, hru0, hAu_fin, hAu⟩ := ih Wu hWu_dim (a + tu • u)
        let ru : ℝ := min ru0 (tu / 2)
        have hru : 0 < ru := lt_min hru0 (by linarith)
        refine ⟨tu, ru, Au, fun _ => ⟨htu, hru, min_le_right _ _, hAu_fin, ?_⟩⟩
        intro w' hw'W hw'0 hw'norm
        have hw'Wu : w' ∈ Wu := by
          refine ⟨⟨w', hw'W⟩, ?_, rfl⟩
          show φ ⟨w', hw'W⟩ = 0
          exact hw'0
        have h := hAu w' hw'Wu (le_trans hw'norm (min_le_left _ _))
        exact ⟨h.1, h.2, hsub_u⟩
      · exact ⟨1, 1, ∅, fun h => False.elim (hu h)⟩
    choose tu ru Au hstep_spec using hstep
    have htu : ∀ u ∈ SW, 0 < tu u := fun u hu => (hstep_spec u hu).1
    have hru : ∀ u ∈ SW, 0 < ru u := fun u hu => (hstep_spec u hu).2.1
    have hru_le : ∀ u ∈ SW, ru u ≤ tu u / 2 := fun u hu => (hstep_spec u hu).2.2.1
    have hAu_fin : ∀ u ∈ SW, (Au u).Finite := fun u hu => (hstep_spec u hu).2.2.2.1
    have hAu : ∀ u ∈ SW, ∀ w' : Fin d → ℝ, w' ∈ W → dotMap u w' = 0 → ‖w'‖ ≤ ru u →
        maxSet K (a + tu u • u + w') ∈ Au u ∧
        maxSet K (a + tu u • u + w') ⊆ maxSet K (a + tu u • u) ∧
        maxSet K (a + tu u • u) ⊆ maxSet K a := fun u hu => (hstep_spec u hu).2.2.2.2
    let ψ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ := fun u v => (dotMap u u)⁻¹ * dotMap u v
    let π : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) := fun u v => v - ψ u v • u
    let U : (Fin d → ℝ) → Set (Fin d → ℝ) := fun u =>
      {v : Fin d → ℝ | 0 < ψ u v ∧ ‖π u v‖ < (ru u / tu u) * ψ u v}
    have hU_open : ∀ u ∈ SW, IsOpen (U u) := by
      intro u _
      have hcont_ψ : Continuous (ψ u) :=
        continuous_const.mul (dotMap u).continuous_of_finiteDimensional
      have hcont_π : Continuous (π u) :=
        continuous_id.sub (hcont_ψ.smul continuous_const)
      exact (isOpen_lt continuous_const hcont_ψ).inter
        (isOpen_lt hcont_π.norm (continuous_const.mul hcont_ψ))
    have hSW_cov : SW ⊆ ⋃ u ∈ SW, U u := by
      intro u huSW
      refine Set.mem_biUnion huSW ?_
      have hu_norm : ‖u‖ = 1 := by simpa using huSW.2
      have hu_ne : u ≠ 0 := by intro h0; simp [h0] at hu_norm
      have hpos : 0 < dotMap u u := dotMap_self_pos hu_ne
      have hψu : ψ u u = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
      have hπu : π u u = 0 := by simp [π, hψu]
      simp only [U, Set.mem_setOf_eq, hψu, hπu, norm_zero, mul_one]
      exact ⟨zero_lt_one, div_pos (hru u huSW) (htu u huSW)⟩
    obtain ⟨F, hF_sub, hF_fin, hF_cov⟩ := hSW_comp.elim_finite_subcover_image hU_open hSW_cov
    obtain ⟨r, hr_pos, hr_le⟩ := aux_exists_pos_le hF_fin.toFinset
      (fun u => tu u / 2)
      (fun u huF => by
        have huSW : u ∈ SW := hF_sub (hF_fin.mem_toFinset.mp huF)
        linarith [htu u huSW])
    let A : Set (Set (Fin d → ℝ)) :=
      insert (maxSet K a) (⋃ u ∈ F, Au u)
    have hA_fin : A.Finite :=
      Set.Finite.insert _ (hF_fin.biUnion (fun u huF => hAu_fin u (hF_sub huF)))
    refine ⟨r, A, hr_pos, hA_fin, ?_⟩
    intro w hwW hwnorm
    by_cases hw0 : w = 0
    · subst hw0
      rw [add_zero]
      exact ⟨Set.mem_insert _ _, Set.Subset.rfl⟩
    · have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      let v : Fin d → ℝ := ‖w‖⁻¹ • w
      have hvW : v ∈ W := W.smul_mem _ hwW
      have hv_norm : ‖v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw_pos),
          inv_mul_cancel₀ (ne_of_gt hw_pos)]
      have hvSW : v ∈ SW := ⟨hvW, by simpa using hv_norm⟩
      have hv_in : v ∈ ⋃ u ∈ F, U u := hF_cov hvSW
      obtain ⟨u, huF, hvU⟩ := Set.mem_iUnion₂.mp hv_in
      have huSW : u ∈ SW := hF_sub huF
      have hu_norm : ‖u‖ = 1 := by simpa using huSW.2
      have hu_ne : u ≠ 0 := by intro h0; simp [h0] at hu_norm
      have hu_dot : 0 < dotMap u u := dotMap_self_pos hu_ne
      simp only [U, Set.mem_setOf_eq] at hvU
      obtain ⟨hψ_pos, hπ_lt⟩ := hvU
      have hrt_le : ru u / tu u ≤ 1 / 2 := by
        rw [div_le_iff₀ (htu u huSW)]
        linarith [hru_le u huSW]
      have hπ_le_half : ‖π u v‖ ≤ (1 / 2) * ψ u v := by
        have := mul_le_mul_of_nonneg_right hrt_le (le_of_lt hψ_pos)
        linarith
      have hψ_le2 : ψ u v ≤ 2 := by
        have h1 : ‖ψ u v • u‖ = ψ u v := by
          rw [norm_smul, hu_norm, mul_one, Real.norm_eq_abs, abs_of_pos hψ_pos]
        have h2 : ψ u v • u = v - π u v := by simp [π]
        have h3 : ‖v - π u v‖ ≤ ‖v‖ + ‖π u v‖ := norm_sub_le v (π u v)
        rw [← h2, h1, hv_norm] at h3
        linarith
      have hr_u : r ≤ tu u / 2 := hr_le u (hF_fin.mem_toFinset.mpr huF)
      have hψw_eq : ψ u w = ‖w‖ * ψ u v := by
        dsimp [ψ, v]
        rw [map_smul, smul_eq_mul]
        ring_nf
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hw_pos), mul_one]
      have hπw_eq : π u w = ‖w‖ • π u v := by
        dsimp [π]
        rw [hψw_eq, smul_sub, mul_smul]
        have hvw : ‖w‖ • v = w := smul_inv_smul₀ (ne_of_gt hw_pos) w
        rw [hvw]
      have hψw_pos : 0 < ψ u w := by rw [hψw_eq]; exact mul_pos hw_pos hψ_pos
      have hψw_le : ψ u w ≤ tu u := by
        rw [hψw_eq]
        have : ‖w‖ ≤ tu u / 2 := le_trans hwnorm hr_u
        nlinarith
      let α : ℝ := ψ u w / tu u
      have hα_pos : 0 < α := div_pos hψw_pos (htu u huSW)
      have hα_le1 : α ≤ 1 := (div_le_one (htu u huSW)).mpr hψw_le
      let w' : Fin d → ℝ := α⁻¹ • π u w
      have hw'W : w' ∈ W := W.smul_mem _ (W.sub_mem hwW (W.smul_mem _ huSW.1))
      have hw'0 : dotMap u w' = 0 := by
        dsimp [w', π, ψ]
        rw [map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
        rw [mul_comm ((dotMap u u)⁻¹ * dotMap u w), ← mul_assoc,
          mul_inv_cancel₀ (ne_of_gt hu_dot), one_mul, sub_self, mul_zero]
      have hw'norm : ‖w'‖ ≤ ru u := by
        dsimp [w']
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα_pos), hπw_eq,
          norm_smul, Real.norm_eq_abs, abs_of_pos hw_pos]
        have hα_inv : α⁻¹ * ‖w‖ = tu u / ψ u v := by
          dsimp [α]
          rw [hψw_eq, inv_div]
          field_simp [ne_of_gt hw_pos, ne_of_gt hψ_pos, ne_of_gt (htu u huSW)]
        rw [← mul_assoc, hα_inv]
        have hlt := mul_lt_mul_of_pos_left hπ_lt (div_pos (htu u huSW) hψ_pos)
        have h_cancel : (tu u / ψ u v) * ((ru u / tu u) * ψ u v) = ru u := by
          field_simp [ne_of_gt hψ_pos, ne_of_gt (htu u huSW)]
        linarith
      obtain ⟨h_in_Au, h_sub1, h_sub2⟩ := hAu u huSW w' hw'W hw'0 hw'norm
      have h_sub_a : maxSet K (a + tu u • u + w') ⊆ maxSet K a := h_sub1.trans h_sub2
      have h_ne : (maxSet K (a + tu u • u + w')).Nonempty :=
        maxSet_nonempty hcompact hKne _
      have h_comb : (1 - α) • a + α • (a + tu u • u + w') = a + w := by
        have h1 : α • (tu u • u) = ψ u w • u := by
          rw [← mul_smul]
          dsimp [α]
          rw [div_mul_cancel₀ _ (ne_of_gt (htu u huSW))]
        have h2 : α • w' = π u w := smul_inv_smul₀ (ne_of_gt hα_pos) (π u w)
        rw [smul_add, smul_add, h1, h2]
        dsimp [π]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have h_eq : maxSet K (a + w) = maxSet K (a + tu u • u + w') := by
        rw [← h_comb]
        exact maxSet_pos_add h_sub_a h_ne (by linarith) hα_pos
      rw [h_eq]
      refine ⟨Set.mem_insert_of_mem _ (Set.mem_biUnion huF h_in_Au), h_sub_a⟩

end Grunbaum2003

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hext : (K.extremePoints ℝ).Infinite)
    (j : ℕ) (hj2 : 2 ≤ j) (hjd : j < d) :
    ∃ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f ∧
      ¬ ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W := by
  by_contra! hproj
  have hKne : K.Nonempty := hext.nonempty.mono extremePoints_subset
  have hproj2 : ∀ L : (Fin d → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective L →
      ∃ W : Set (Fin 2 → ℝ), W.Finite ∧ L '' K = convexHull ℝ W :=
    aux_proj_two_of_proj_j hj2 hjd K hproj
  have htop_dim : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  obtain ⟨r, A, hr_pos, hA_fin, hA⟩ :=
    aux_finite_faces_wedge hcompact hKne hproj2 d ⊤ htop_dim 0
  have h_all_in_A : ∀ a : Fin d → ℝ, maxSet K a ∈ A := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      have := (hA 0 (Submodule.zero_mem ⊤) (by simp [le_of_lt hr_pos])).1
      simpa using this
    · have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      let c : ℝ := r / ‖a‖
      have hc_pos : 0 < c := div_pos hr_pos ha_pos
      have hcnorm : ‖c • a‖ ≤ r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos, div_mul_cancel₀ _ (ne_of_gt ha_pos)]
      have h1 := (hA (c • a) (Submodule.mem_top) hcnorm).1
      rw [zero_add, maxSet_smul_pos K a hc_pos] at h1
      exact h1
  let A_ne : Set (Set (Fin d → ℝ)) := {F ∈ A | (F ∩ K).Nonempty}
  have hAne_fin : A_ne.Finite := hA_fin.subset (fun _ h => h.1)
  let pick : A_ne → (Fin d → ℝ) := fun F => F.2.2.choose
  let S : Set (Fin d → ℝ) := Set.range pick
  have hS_fin : S.Finite := by
    haveI : Finite A_ne := hAne_fin.to_subtype
    exact Set.finite_range pick
  have hS_sub : S ⊆ K := by
    rintro x ⟨F, rfl⟩
    exact F.2.2.choose_spec.2
  have hK_sub : K ⊆ convexHull ℝ S := by
    intro x0 hx0K
    by_contra hx0_not
    obtain ⟨φ, u, hφS, hφx0⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ S) (hS_fin.isClosed_convexHull ℝ) hx0_not
    let aφ : Fin d → ℝ := fun i => φ (Pi.single i 1)
    have hφ_eq : ∀ x : Fin d → ℝ, φ x = dotMap aφ x := by
      intro x
      have hx_sum : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hx_sum]
      rw [map_sum]
      simp only [dotMap_apply, aφ, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hFa_in : maxSet K aφ ∈ A := h_all_in_A aφ
    obtain ⟨p0, hp0⟩ := maxSet_nonempty hcompact hKne aφ
    have hFa_ne : (maxSet K aφ ∩ K).Nonempty := ⟨p0, hp0, hp0.1⟩
    let Fφ : A_ne := ⟨maxSet K aφ, hFa_in, hFa_ne⟩
    let p : Fin d → ℝ := pick Fφ
    have hp_in : p ∈ maxSet K aφ ∩ K := Fφ.2.2.choose_spec
    have hpS : p ∈ S := ⟨Fφ, rfl⟩
    have hφp_lt : φ p < u := hφS p (subset_convexHull ℝ S hpS)
    have h_le : dotMap aφ x0 ≤ dotMap aφ p := hp_in.1.2 x0 hx0K
    rw [← hφ_eq x0, ← hφ_eq p] at h_le
    linarith
  have hK_eq : K = convexHull ℝ S :=
    Set.Subset.antisymm hK_sub (convexHull_min hS_sub hconvex)
  have hext_sub : K.extremePoints ℝ ⊆ S := by
    rw [hK_eq]
    exact extremePoints_convexHull_subset
  exact hext (hS_fin.subset hext_sub)
