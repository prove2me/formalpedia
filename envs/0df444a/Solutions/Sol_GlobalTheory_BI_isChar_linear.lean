-- Prove2me | solution 1 for GlobalTheory.BI.isChar_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:11.841186+00:00
-- url     : https://prove2.me/submissions/0cb72419-3cd3-4b5c-ac8b-523571bfbb7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  intro K L _ _ _ G _ m ζ lam hm hζ hG
  haveI : NeZero m := ⟨hm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hζ' : IsPrimitiveRoot (algebraMap K L ζ) m := hζ.map_of_injective hinj
  have h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L) := by
    intro g
    have h1 : (lam g : L) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  choose μ hμ using h
  let μ' : G →* K :=
    { toFun := μ
      map_one' := hinj (by rw [hμ]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }
  refine ⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩
  have : Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g := by
    change LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]
    simp
  rw [this, hμ]
end GlobalTheory.BI
