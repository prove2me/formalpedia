-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_short_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:27.632993+00:00
-- url     : https://prove2.me/submissions/e5d3fa05-7871-465f-8775-cacf4f75b3be

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_forall_inner_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_finite_latticeDual_norm_le
import Theorems.Thm_GroundTheory_Automorphic_shortBasisBound_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
namespace GroundTheory.Automorphic
theorem _root_.solution (N : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X], finrank ℝ X = N → ∀ (L : AddSubgroup X) (μ : ℝ), 0 < μ →
    span ℝ (L : Set X) = ⊤ → span ℝ (latticeDual L : Set X) = ⊤ →
    (∀ y ∈ latticeDual L, y ≠ 0 → μ ≤ ‖y‖) →
    ∃ e : Fin N → X, LinearIndependent ℝ e ∧ ∀ i, e i ∈ L ∧ ‖e i‖ ≤ shortBasisBound N μ := by
  induction N with
  | zero =>
    intro X _ _ _ _ L μ _ _ _ _
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ N ih =>
    intro X _ _ _ hdim L μ hμ hLspan hDspan hmin
    classical
    have : Nontrivial X := nontrivial_of_finrank_eq_succ hdim

    obtain ⟨y0, hy0, hy0ne⟩ : ∃ y ∈ latticeDual L, y ≠ 0 := by
      by_contra h
      push Not at h
      have hsub : (latticeDual L : Set X) ⊆ {0} := fun y hy => h y hy
      have hle := span_mono (R := ℝ) hsub
      rw [hDspan, span_singleton_eq_bot.2 rfl] at hle
      exact top_ne_bot (eq_bot_iff.2 hle)

    obtain ⟨w, ⟨⟨hwD, -⟩, hw0⟩, hwmin⟩ := Set.exists_min_image
      ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ ‖y0‖} ∩ {y | y ≠ 0}) (fun y => ‖y‖)
      ((finite_latticeDual_norm_le hLspan ‖y0‖).subset Set.inter_subset_left)
      ⟨y0, ⟨hy0, le_rfl⟩, hy0ne⟩
    have hwmin' : ∀ y ∈ latticeDual L, y ≠ 0 → ‖w‖ ≤ ‖y‖ := by
      intro y hy hyne
      by_cases h : ‖y‖ ≤ ‖y0‖
      · exact hwmin y ⟨⟨hy, h⟩, hyne⟩
      · exact (hwmin y0 ⟨⟨hy0, le_rfl⟩, hy0ne⟩).trans (le_of_not_ge h)
    have hwμ : μ ≤ ‖w‖ := hmin w hwD hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0

    have hx1 : ∃ x ∈ L, ⟪w, x⟫ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (eq_zero_of_forall_inner_eq_zero hLspan h)
    have hex : ∃ n : ℕ, 0 < n ∧ ∃ x ∈ L, ⟪w, x⟫ = n := by
      obtain ⟨x1, hx1L, hx1⟩ := hx1
      obtain ⟨m, hm⟩ := hwD x1 hx1L
      have hm0 : m ≠ 0 := by rintro rfl; exact hx1 (by simpa using hm)
      rcases lt_or_gt_of_ne hm0 with hneg | hpos
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, -x1, neg_mem hx1L, ?_⟩
        rw [inner_neg_right, hm, Nat.cast_natAbs, Int.cast_abs,
          abs_of_neg (by exact_mod_cast hneg)]
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, x1, hx1L, ?_⟩
        rw [hm, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    obtain ⟨hn0pos, x0, hx0L, hx0⟩ := Nat.find_spec hex
    have hdiv : ∀ x ∈ L, ∃ q : ℤ, ⟪w, x⟫ = q * (Nat.find hex : ℝ) := by
      intro x hx
      obtain ⟨m, hm⟩ := hwD x hx
      set n0 := Nat.find hex
      have hn0z : (0 : ℤ) < n0 := by exact_mod_cast hn0pos
      set r := m % (n0 : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ hn0z.ne'
      have hrlt : r < n0 := Int.emod_lt_of_pos _ hn0z
      have hmr : m = r + n0 * (m / n0) := (Int.emod_add_mul_ediv m n0).symm
      have hxr : x - (m / (n0 : ℤ)) • x0 ∈ L := sub_mem hx (zsmul_mem hx0L _)
      have hval : ⟪w, x - (m / (n0 : ℤ)) • x0⟫ = r := by
        rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hm, hx0]
        have : (m : ℝ) = r + n0 * (m / (n0 : ℤ) : ℤ) := by exact_mod_cast hmr
        rw [this]; ring
      have hr : r = 0 := by
        by_contra hrne
        have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
        have := Nat.find_min hex (m := r.toNat) (by omega)
        apply this
        refine ⟨by omega, _, hxr, ?_⟩
        rw [hval]
        have : ((r.toNat : ℤ) : ℝ) = r := by rw [Int.toNat_of_nonneg hr0]
        rw [← this]; norm_cast
      refine ⟨m / n0, ?_⟩
      have hm' : m = (m / n0) * n0 := by rw [hr] at hmr; linarith
      rw [hm]
      exact_mod_cast hm'
    have hn0 : Nat.find hex = 1 := by
      by_contra hne
      have hge : (2 : ℝ) ≤ Nat.find hex := by
        have : 2 ≤ Nat.find hex := by omega
        exact_mod_cast this
      set n0 := Nat.find hex
      have hw'D : (n0 : ℝ)⁻¹ • w ∈ latticeDual L := by
        intro x hx
        obtain ⟨q, hq⟩ := hdiv x hx
        refine ⟨q, ?_⟩
        rw [real_inner_smul_left, hq]
        field_simp
      have hw'0 : (n0 : ℝ)⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero (by linarith)) hw0
      have h1 := hwmin' _ hw'D hw'0
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)] at h1
      have : (n0 : ℝ)⁻¹ * ‖w‖ < ‖w‖ := by
        have : (n0 : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; gcongr
        nlinarith
      linarith
    rw [hn0, Nat.cast_one] at hx0

    have : Fact (finrank ℝ X = N + 1) := ⟨hdim⟩
    set W : Submodule ℝ X := (ℝ ∙ w)ᗮ with hWdef
    have hWdim : finrank ℝ W = N := finrank_orthogonal_span_singleton hw0
    have memW : ∀ z : X, z ∈ W ↔ ⟪w, z⟫ = 0 := fun z => mem_orthogonal_singleton_iff_inner_right
    let M : AddSubgroup W := L.comap W.subtype.toAddMonoidHom
    have memM : ∀ m : W, m ∈ M ↔ (m : X) ∈ L := fun m => Iff.rfl

    let P : X →ₗ[ℝ] W :=
      { toFun := fun x => ⟨x - ⟪w, x⟫ • x0, by
          rw [memW, inner_sub_right, real_inner_smul_right, hx0]; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_smul] }
    have hP : ∀ x, (P x : X) = x - ⟪w, x⟫ • x0 := fun _ => rfl
    have hPL : ∀ x ∈ L, P x ∈ M := by
      intro x hx
      obtain ⟨n, hn⟩ := hwD x hx
      rw [memM, hP, hn, Int.cast_smul_eq_zsmul]
      exact sub_mem hx (zsmul_mem hx0L _)
    have hPW : ∀ z : W, P z = z := by
      intro z
      ext
      rw [hP, (memW z).1 z.2, zero_smul, sub_zero]
    have hPsurj : LinearMap.range P = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hPW z⟩
    have hMspan : span ℝ (M : Set W) = ⊤ := by
      apply eq_top_iff.2
      rw [← hPsurj, LinearMap.range_eq_map, ← hLspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hPL x hx)

    let π : X →ₗ[ℝ] W :=
      { toFun := fun z => ⟨z - (⟪w, z⟫ / ‖w‖ ^ 2) • w, by
          rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_div, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_div_assoc,
            mul_smul] }
    have hπ : ∀ z, (π z : X) = z - (⟪w, z⟫ / ‖w‖ ^ 2) • w := fun _ => rfl
    have hπW : ∀ z : W, π z = z := by
      intro z
      ext
      rw [hπ, (memW z).1 z.2, zero_div, zero_smul, sub_zero]
    have hπD : ∀ z ∈ latticeDual L, π z ∈ latticeDual M := by
      intro z hz m hm
      obtain ⟨n, hn⟩ := hz m hm
      refine ⟨n, ?_⟩
      rw [coe_inner, hπ, inner_sub_left, real_inner_smul_left, (memW m).1 m.2, mul_zero, sub_zero, hn]
    have hMDspan : span ℝ (latticeDual M : Set W) = ⊤ := by
      apply eq_top_iff.2
      have hπsurj : LinearMap.range π = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hπW z⟩
      rw [← hπsurj, LinearMap.range_eq_map, ← hDspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hπD x hx)

    have hMmin : ∀ y ∈ latticeDual M, y ≠ 0 → Real.sqrt 3 / 2 * μ ≤ ‖y‖ := by
      intro y hy hyne
      have hyw : ⟪(y : X), w⟫ = 0 := by rw [real_inner_comm]; exact (memW y).1 y.2
      set c := ⟪(y : X), x0⟫
      set s : ℝ := (round c : ℝ) - c
      have hs : |s| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round c
      set z := (y : X) + s • w
      have hzD : z ∈ latticeDual L := by
        intro x hx
        obtain ⟨n, hn⟩ := hwD x hx
        obtain ⟨k, hk⟩ := hy (P x) (hPL x hx)
        refine ⟨k + round c * n, ?_⟩
        rw [coe_inner, hP, inner_sub_right, real_inner_smul_right, hn] at hk
        rw [inner_add_left, real_inner_smul_left, hn]
        push_cast
        simp only [s]
        linear_combination hk
      have hz0 : z ≠ 0 := by
        intro h
        have : ⟪(y : X), z⟫ = ‖(y : X)‖ ^ 2 := by
          rw [inner_add_right, real_inner_smul_right, hyw, mul_zero, add_zero,
            real_inner_self_eq_norm_sq]
        rw [h, inner_zero_right] at this
        have hy0 : (y : X) = 0 := by
          have : ‖(y : X)‖ = 0 := by nlinarith [norm_nonneg (y : X)]
          exact norm_eq_zero.1 this
        exact hyne (Subtype.ext hy0)
      have hz := hwmin' z hzD hz0
      have hzn : ‖z‖ ^ 2 = ‖(y : X)‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, hyw, norm_smul, Real.norm_eq_abs, mul_pow,
          sq_abs]
        ring
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := abs_le.1 hs
        nlinarith
      have hsq : (Real.sqrt 3 / 2 * μ) ^ 2 ≤ ‖y‖ ^ 2 := by
        have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have hw2 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        have hμ2 : μ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hμ.le hwμ 2
        have : ‖y‖ = ‖(y : X)‖ := rfl
        rw [mul_pow, div_pow, h3, this]
        nlinarith
      exact le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _) |>.trans_eq' rfl

    obtain ⟨e', hli', he'⟩ := ih (X := W) hWdim M (Real.sqrt 3 / 2 * μ) (by positivity) hMspan
      hMDspan hMmin
    set R' := shortBasisBound N (Real.sqrt 3 / 2 * μ)
    have hR' : 0 ≤ R' := shortBasisBound_nonneg N (by positivity)
    have hspan' : ⊤ ≤ span ℝ (Set.range e') := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        have : Subsingleton W := finrank_zero_iff.1 hWdim
        intro z _
        rw [Subsingleton.elim z 0]; exact zero_mem _
      · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        exact (hli'.span_eq_top_of_card_eq_finrank (by simp [hWdim])).ge
    let B := Basis.mk hli' hspan'

    set q : W := ⟨x0 - (‖w‖ ^ 2)⁻¹ • w, by
      rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx0]
      field_simp; ring⟩
    set c := B.repr q
    set x0' := x0 - ∑ i, ⌊c i⌋ • (e' i : X)
    have hx0'L : x0' ∈ L := sub_mem hx0L (sum_mem fun i _ => zsmul_mem (he' i).1 _)
    have hq : (q : X) = ∑ i, c i • (e' i : X) := by
      conv_lhs => rw [← B.sum_repr q]
      rw [coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_smul, Basis.mk_apply]
    have hx0'eq : x0' = ∑ i, Int.fract (c i) • (e' i : X) + (‖w‖ ^ 2)⁻¹ • w := by
      have hx0q : x0 = (q : X) + (‖w‖ ^ 2)⁻¹ • w := by simp [q]
      simp only [x0']
      rw [hx0q, hq]
      have : ∀ i, Int.fract (c i) • (e' i : X) = c i • (e' i : X) - ⌊c i⌋ • (e' i : X) := by
        intro i
        rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
      simp only [this, Finset.sum_sub_distrib]
      abel
    have hx0'norm : ‖x0'‖ ≤ N * R' + μ⁻¹ := by
      rw [hx0'eq]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans ?_
        have : ∀ i, ‖Int.fract (c i) • (e' i : X)‖ ≤ R' := by
          intro i
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
          have h1 := (he' i).2
          have h2 := (Int.fract_lt_one (c i)).le
          have : ‖(e' i : X)‖ = ‖e' i‖ := rfl
          rw [this]
          nlinarith [norm_nonneg (e' i), Int.fract_nonneg (c i)]
        refine (Finset.sum_le_sum fun i _ => this i).trans ?_
        simp
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), sq, mul_inv, mul_assoc,
          inv_mul_cancel₀ hwpos.ne', mul_one]
        exact inv_anti₀ hμ hwμ
    have hx0'w : ⟪w, x0'⟫ = 1 := by
      simp only [x0', inner_sub_right, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
      rw [hx0]
      have : ∀ i, ⟪w, (e' i : X)⟫ = 0 := fun i => (memW _).1 (e' i).2
      simp [this]
    refine ⟨Fin.cons x0' fun i => (e' i : X), ?_, ?_⟩
    · rw [linearIndependent_finCons]
      refine ⟨hli'.map' W.subtype (ker_subtype W), ?_⟩
      intro hmem
      have hle : span ℝ (Set.range fun i => (e' i : X)) ≤ W :=
        span_le.2 (by rintro _ ⟨i, rfl⟩; exact (e' i).2)
      have := (memW _).1 (hle hmem)
      rw [hx0'w] at this
      exact one_ne_zero this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hx0'L, by simpa [shortBasisBound] using hx0'norm⟩
      · refine ⟨(he' j).1, ?_⟩
        simp only [Fin.cons_succ, shortBasisBound]
        have h1 : ‖(e' j : X)‖ ≤ R' := (he' j).2
        have hN1 : (1 : ℝ) ≤ N := by
          have : 0 < N := Fin.pos j
          exact_mod_cast this
        have : R' ≤ N * R' := le_mul_of_one_le_left hR' hN1
        have : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ.le
        linarith
end GroundTheory.Automorphic
