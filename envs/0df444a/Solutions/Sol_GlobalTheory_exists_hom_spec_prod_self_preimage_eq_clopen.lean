-- Prove2me | solution 1 for GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:36.253481+00:00
-- url     : https://prove2.me/submissions/2c23c655-8f48-4d9c-aff5-a8ea22c3c8ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomSpecProdSelfPreimageEqClopen
import Theorems.Thm_GlobalTheory_exists_idempotent_basicOpen_eq_of_isClopen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U →
      ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧
        ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  intro O _ T p U hU
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen T U hU
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom
  let ψ : O × O →+* Γ(T, ⊤) :=
    { toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination -(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hψ : ψ.comp (algebraMap O (O × O)) = φ := by
    ext a
    change φ a * ε + φ a * (1 - ε) = φ a
    ring
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · have : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop := rfl
    rw [Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · rw [Scheme.preimage_basicOpen_top, ← hεU]
    congr 2
    have h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
      have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun f => f.hom (fst1 O)) this
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
      refine h2.trans ?_
      simp [fst1]
    rw [h1]
    change φ 1 * ε + φ 0 * (1 - ε) = ε
    simp
end GlobalTheory
