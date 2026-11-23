-- Prove2me | solution 1 for GlobalTheory.heisenberg_weightSpace_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:46.360727+00:00
-- url     : https://prove2.me/submissions/d5ded87c-b58d-43b4-8066-1f9bf3e98d55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Theorems.Thm_GlobalTheory_linearIndependent_of_comm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem
end GlobalTheory
