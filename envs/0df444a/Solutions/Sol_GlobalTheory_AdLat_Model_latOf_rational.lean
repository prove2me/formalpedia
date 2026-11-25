-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.latOf_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:58.412728+00:00
-- url     : https://prove2.me/submissions/37d4695d-ff75-43f7-80ff-15a5d6fa63af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
theorem _root_.solution {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) :
    latOf F (γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E)) L = latOf F 1 (γ.mulVec '' L) := by
  set g := γ.map fun e => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e : RA F E) with hg
  have h1 : ∀ (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E),
      g.mulVec (fun i => a ⊗ₜ x i) = fun i => a ⊗ₜ γ.mulVec x i := by
    intro a x
    funext i
    simp [hg, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
  have h2 : (hat F L).map (Matrix.mulVecLin g).toAddMonoidHom = hat F (γ.mulVec '' L) := by
    unfold hat
    rw [AddMonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, h1 a x⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, ha, x, hx, rfl⟩, h1 a x⟩
  ext w
  simp only [latOf, Set.mem_setOf_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe, ← h2, AddSubgroup.mem_map]
  rfl
end GlobalTheory.AdLat.Model
