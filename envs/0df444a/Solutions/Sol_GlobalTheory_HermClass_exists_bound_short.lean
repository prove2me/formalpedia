-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_bound_short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:43.566187+00:00
-- url     : https://prove2.me/submissions/b40e68d2-e69a-4eaa-8bc6-9ec60086d5f3

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral_of_trace
import Theorems.Thm_GlobalTheory_HermClass_isIntegral_star
import Theorems.Thm_GlobalTheory_HermClass_trace_star
import Theorems.Thm_GlobalTheory_HermClass_det_ne_zero_and_abs_le
import Theorems.Thm_GlobalTheory_HermClass_exists_short_of_trace_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HermClass
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ C : ℝ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, v ≠ 0 ∧ ∀ φ : E →+* ℂ, ‖φ (h v v)‖ ≤ C := by
  classical
  obtain ⟨D, hD, hDa⟩ := exists_int_mul_isIntegral_of_trace E
  set F := maximalRealSubfield E with hF
  have hM0 : N * D * 2 ≠ 0 := by positivity
  refine ⟨(2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) ^ 2, ?_⟩
  intro V _ _ _ h Λ hV hs hfg hsp hO hdual
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_compHom ℚ E V
  have : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 hfg
  have : IsAddTorsionFree V := .of_module_rat V
  have : Module.Free ℤ Λ := inferInstance
  let β := Module.Free.chooseBasis ℤ Λ
  let κ := Module.Free.ChooseBasisIndex ℤ Λ
  let b : κ → V := fun i => β i
  have hbZ : LinearIndependent ℤ b := β.linearIndependent.map' Λ.subtype (ker_subtype Λ)
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hbZ
  have hbΛ : ∀ x ∈ Λ, ∃ c : κ → ℤ, x = ∑ i, c i • b i := fun x hx =>
    ⟨β.repr ⟨x, hx⟩, by
      have := congrArg Λ.subtype (β.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      exact this.symm⟩
  have hbs : ⊤ ≤ span ℚ (Set.range b) := by
    have hΛ : ∀ x ∈ Λ, x ∈ span ℚ (Set.range b) := fun x hx => by
      obtain ⟨c, rfl⟩ := hbΛ x hx
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    have key : ∀ x ∈ span E (Λ : Set V), ∀ a : E, a • x ∈ span ℚ (Set.range b) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro a
        obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton a)
        have h1 := smul_mem _ (M : ℚ)⁻¹ (hΛ _ (hO _ (hMa a rfl) x hx))
        rw [← smul_assoc, ← smul_mul_assoc, Algebra.smul_def] at h1
        have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
        simpa [hM'] using h1
      | zero => intro a; simp
      | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
      | smul c x _ hx => intro a; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hsp ▸ mem_top) 1
  have hFV : finrank F V = 2 * n := by
    rw [← finrank_mul_finrank F E V, hV, Algebra.IsQuadraticExtension.finrank_eq_two]
  have : FiniteDimensional F V := Module.Finite.trans E V
  have hκ : Fintype.card κ = finrank ℚ F * finrank F V := by
    rw [← finrank_eq_card_basis (Basis.mk hbQ hbs), ← finrank_mul_finrank ℚ E V,
      ← finrank_mul_finrank F E V, ← finrank_mul_finrank ℚ F E, mul_assoc]
  have hreal : ∀ x y, h x y + h y x ∈ F := fun x y => by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star _ = _
    rw [star_add, ← hs, ← hs, add_comm]
  have hstF : ∀ c : F, starRingEnd E (c : E) = c := fun c => IsCMField.complexConj_apply_eq_self E c
  let q : LinearMap.BilinForm F V := LinearMap.mk₂ F (fun x y => ⟨h x y + h y x, hreal x y⟩)
    (fun x x' y => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
    (fun x y y' => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
  have hq : ∀ x y, (q x y : E) = h x y + h y x := fun _ _ => rfl
  have hqs : LinearMap.IsSymm q := ⟨fun x y => Subtype.ext (by simp [hq, add_comm])⟩
  have htr : ∀ x y, Algebra.trace ℚ F (q x y) = Algebra.trace ℚ E (h x y) := fun x y => by
    have h1 := Algebra.trace_trace (R := ℚ) (S := F) (T := E) (algebraMap F E (q x y))
    rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_nsmul] at h1
    have h2 : algebraMap F E (q x y) = h x y + star (h x y) := by rw [← hs]; rfl
    rw [h2, map_add, trace_star, two_nsmul] at h1
    linarith
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  obtain ⟨hT0, hT1⟩ := det_ne_zero_and_abs_le T hM0 (by
    intro x hx i
    set y : V := ∑ i, x i • b i with hy
    have h1 : ∀ j, ∃ m : ℤ, Algebra.trace ℚ E (h y (b j)) = m := fun j => by
      obtain ⟨m, hm⟩ := hx j
      refine ⟨m, ?_⟩
      rw [← hm, hy, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul, map_smul, ← htr]
      rfl
    have h2 : ∀ w ∈ Λ, ∃ m : ℤ, Algebra.trace ℚ E (h y w) = m := fun w hw => by
      obtain ⟨c, rfl⟩ := hbΛ w hw
      choose m hm using h1
      refine ⟨∑ j, c j * m j, ?_⟩
      rw [map_sum, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, hm, zsmul_eq_mul, Int.cast_mul]
    have h3 : (N : E) • (D : E) • y ∈ Λ := hdual _ fun w hw => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine hDa _ fun t ht => ?_
      obtain ⟨m, hm⟩ := h2 _ (hO _ (isIntegral_star ht) w hw)
      exact ⟨m, by rw [← hm, map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]⟩
    obtain ⟨c, hc⟩ := hbΛ _ h3
    have h4 : ∑ i, ((N : ℚ) * D * x i - c i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, ← hc, mul_smul,
        ← Finset.smul_sum, ← hy, sub_self]
    have h5 := Fintype.linearIndependent_iff.1 hbQ _ h4 i
    exact ⟨2 * c i, by push_cast; linarith⟩)
  have hcard : Fintype.card κ ≠ 0 := by
    rw [hκ, hFV]; exact mul_ne_zero finrank_pos.ne' (by omega)
  set M : ℝ := |((N * D * 2 : ℤ) : ℝ)| with hM
  have hM' : 0 ≤ M := abs_nonneg _
  obtain ⟨z, hz0, hz⟩ := exists_short_of_trace_det q hqs b hκ (t := M + 1) (by positivity) hT0 (by
    have h1 : |((T.det : ℚ) : ℝ)| ≤ M ^ Fintype.card κ := by rw [hM]; exact_mod_cast hT1
    have h2 : M ^ Fintype.card κ < (M + 1) ^ Fintype.card κ :=
      pow_lt_pow_left₀ (by linarith) hM' hcard
    have h3 : 1 ≤ (M + 1) ^ Fintype.card κ := one_le_pow₀ (by linarith)
    refine h1.trans_lt (h2.trans_le ?_)
    nlinarith)
  refine ⟨∑ i, z i • b i, sum_mem fun i _ => Λ.smul_mem _ (β i).2, fun h0 => hz0 ?_, fun φ => ?_⟩
  · exact funext (Fintype.linearIndependent_iff.1 hbZ z h0)
  · have h1 := hz (φ.comp (algebraMap F E))
    rw [hFV] at h1
    refine le_trans ?_ h1
    change _ ≤ ‖φ (h _ _ + h _ _)‖
    rw [← two_mul, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
    linarith [norm_nonneg (φ (h (∑ i, z i • b i) (∑ i, z i • b i)))]
end GlobalTheory.HermClass
