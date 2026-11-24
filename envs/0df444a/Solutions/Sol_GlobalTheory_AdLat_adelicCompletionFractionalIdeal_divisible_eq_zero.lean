-- Prove2me | solution 1 for GlobalTheory.AdLat.adelicCompletionFractionalIdeal_divisible_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:38.435924+00:00
-- url     : https://prove2.me/submissions/990c708c-c224-41e0-80a7-6af50fb0aa68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_cap_gen_mem
import Theorems.Thm_GlobalTheory_T_adelicCompletion_lattice_separated_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
namespace GlobalTheory.AdLat
theorem _root_.solution (J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ hat1 F (J : Set E), z = N • w) : z = 0 := by
  let ι : E →ₗ[𝓞 E] (Fin 1 → E) := LinearMap.pi fun _ => LinearMap.id
  have hfg : ((J : Submodule (𝓞 E) E).map ι).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map ι
  have hm : ∀ w ∈ hat1 F (J : Set E), (fun _ => w : Fin 1 → RA F E) ∈
      hat F (((J : Submodule (𝓞 E) E).map ι : Submodule (𝓞 E) (Fin 1 → E)) : Set (Fin 1 → E)) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact cap_gen_mem F _ a ha (ι x) (Submodule.mem_map_of_mem hx)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  have := (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E 1 _ hfg).1 (fun _ => z) (fun N hN => by
    obtain ⟨w, hw, rfl⟩ := h N hN
    exact ⟨_, hm w hw, rfl⟩)
  exact congrFun this 0
end GlobalTheory.AdLat
