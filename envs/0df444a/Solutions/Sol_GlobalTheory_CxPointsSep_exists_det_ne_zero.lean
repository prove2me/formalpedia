-- Prove2me | solution 1 for GlobalTheory.CxPointsSep.exists_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:21.004344+00:00
-- url     : https://prove2.me/submissions/a5a620e2-b7c2-4bfe-a725-a9f4f28f567c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom
import Theorems.Thm_GlobalTheory_CxPointsSep_eq_zero_of_forall_algHom
import Theorems.Thm_GlobalTheory_CxPointsSep_isReduced_complex_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep
namespace GlobalTheory.CxPointsSep
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0
      rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero
end GlobalTheory.CxPointsSep
