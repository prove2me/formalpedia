-- Prove2me | solution 1 for M4aHerbrand.mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0c3d9857-80e9-55b8-b0ca-6a2e2fc41d5b

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory
open scoped NumberField.PlaceTransport

namespace C5Aux

variable (F : Type) [Field F] [NumberField F]

open Classical in

noncomputable def probeFin (w : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk (fun v => if v = w then (-1 : v.adicCompletion F) else 1)
    (Filter.Eventually.of_forall fun v => by
      change (if v = w then (-1 : v.adicCompletion F) else 1) ∈ v.adicCompletionIntegers F
      split_ifs
      · exact neg_mem (one_mem _)
      · exact one_mem _)

open Classical in
theorem probeFin_apply (w v : HeightOneSpectrum (𝓞 F)) :
    probeFin F w v = if v = w then (-1 : v.adicCompletion F) else 1 := rfl

theorem probeFin_apply_mem (w v : HeightOneSpectrum (𝓞 F)) : probeFin F w v ∈ v.adicCompletionIntegers F := by
  rw [probeFin_apply]
  split_ifs
  · exact neg_mem (one_mem _)
  · exact one_mem _

theorem probeFin_mul_self (w : HeightOneSpectrum (𝓞 F)) : probeFin F w * probeFin F w = 1 := by
  refine FiniteAdeleRing.ext _ fun v => ?_
  change probeFin F w v * probeFin F w v = 1
  rw [probeFin_apply]
  split_ifs <;> simp

noncomputable def probe (w : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.mkOfMulEqOne ((1 : InfiniteAdeleRing F), probeFin F w) ((1 : InfiniteAdeleRing F), probeFin F w)
    (Prod.ext (one_mul _) (probeFin_mul_self F w))

theorem coe_probe (w : HeightOneSpectrum (𝓞 F)) :
    (probe F w : AdeleRing (𝓞 F) F) = ((1 : InfiniteAdeleRing F), probeFin F w) := rfl

theorem probe_mem (T : Set (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) :
    probe F w ∈ unitIdelesTrivialOn (𝓞 F) F T := by
  refine (mem_unitIdelesTrivialOn_iff T _).2 ⟨fun v _ => ⟨probeFin_apply_mem F w v, probeFin_apply_mem F w v⟩, ?_, fun v hv => ?_⟩
  · exact Units.ext rfl
  · refine Units.ext ?_
    rw [coe_finPart_apply, coe_probe, Units.val_one]
    change probeFin F w v = 1
    rw [probeFin_apply, if_neg (fun h : v = w => hw (h ▸ hv))]

end C5Aux

open C5Aux in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x)
    (w w' : HeightOneSpectrum (𝓞 F)) (h : w.under (𝓞 E) = w'.under (𝓞 E)) :
    w ∈ T ↔ w' ∈ T := by
  classical

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  suffices key : ∀ w₁ w₂ : HeightOneSpectrum (𝓞 F), w₁.under (𝓞 E) = w₂.under (𝓞 E) → w₁ ∉ T → w₂ ∉ T by
    constructor
    · intro hw; by_contra hw'; exact key w' w h.symm hw' hw
    · intro hw'; by_contra hw; exact key w w' h hw hw'
  intro w₁ w₂ h12 h1 h2

  have horb : w₂ ∈ MulAction.orbit (F ≃ₐ[E] F) w₁ := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E F w₁]
    exact h12.symm
  obtain ⟨σ, hσ⟩ := horb

  have hx := probe_mem F T w₁ h1
  have hσx : (GenuineDescent.genuineDescentDatum E F).unitsAct σ (probe F w₁) ∈ unitIdelesTrivialOn (𝓞 F) F T := by
    rw [← hactU σ ⟨probe F w₁, hx⟩]
    exact Subtype.mem _
  have h3 := congrArg (fun u : (w₂.adicCompletion F)ˣ => (u : w₂.adicCompletion F)) (hσx.2.2 w₂ h2)
  change (((GenuineDescent.genuineDescentDatum E F).act σ (probe F w₁ : AdeleRing (𝓞 F) F)).2 w₂) =
    ((1 : (w₂.adicCompletion F)ˣ) : w₂.adicCompletion F) at h3

  rw [Units.val_one, GenuineDescent.genuineDescentDatum_act_snd_apply E F σ _ hσ, coe_probe] at h3
  change NumberField.PlaceTransport.transport σ hσ (probeFin F w₁ w₁) = 1 at h3
  rw [probeFin_apply, if_pos rfl, map_neg, map_one] at h3
  haveI : CharZero (w₂.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have h4 : (2 : w₂.adicCompletion F) = 0 := by linear_combination -h3
  exact two_ne_zero h4

end S_M4aHerbrand_mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn
end P2MW
export P2MW.S_M4aHerbrand_mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn (solution)
