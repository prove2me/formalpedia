-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KModExists.kModExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:44.212993+00:00
-- url     : https://prove2.me/submissions/3908e748-3630-4dc0-9ee3-697c61c57cad

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
import Theorems.Thm_GlobalTheory_CompanionTheory_KModExists_kHighest_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_KModExists_glRel_of_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.KModExists
theorem _root_.solution (h1 : SmMod) (h2 : KFinSm) (h3 : KFinStab) (h4 : StabLink) (h5 : HWofType) (h6 : TypeOfHW) :
    CompanionTheory.D.LK.KModExists := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨S, E, hS⟩ := h1 n ε H σ hσ
  obtain ⟨V₀, hV, hst⟩ := h3 n ε H σ S E hσ hS
  have hsm : ∀ v, IsKFin ε σ v → v ∈ S := fun v hv => (hS.mem v).2 (h2 n ε H σ hσ hirr v hv)
  set D : Submodule ℂ H := V₀.map S.subtype with hD
  have hmem : ∀ v, v ∈ D ↔ IsKFin ε σ v := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hV x).1 hx
    · intro hv
      exact ⟨⟨v, hsm v hv⟩, (hV _).2 hv, rfl⟩
  have hDS : D ≤ S := fun v hv => hsm v ((hmem v).1 hv)
  let ι : D →ₗ[ℂ] S := Submodule.inclusion hDS
  have hι : Function.Injective ι := Submodule.inclusion_injective hDS
  have hin : ∀ a b (v : D), (S.subtype ∘ₗ E a b ∘ₗ ι) v ∈ D := fun a b v =>
    ⟨E a b (ι v), hst a b _ ((hV _).2 ((hmem _).1 v.2)), rfl⟩
  let E' : Fin n → Fin n → Module.End ℂ D := fun a b => LinearMap.codRestrict D (S.subtype ∘ₗ E a b ∘ₗ ι) (hin a b)
  have hE' : ∀ a b v, ι (E' a b v) = E a b (ι v) := fun a b v => Subtype.ext rfl
  have hT : ∀ T : Submodule ℂ H, FiniteDimensional ℂ T → IsKStableOn ε σ T → T ≤ D :=
    fun T hf hs v hv => (hmem v).2 ⟨T, hf, hv, hs⟩
  refine ⟨D, E', hmem, fun X hX v => hS.real X hX (ι v), glRel_of_inj ι hι E' E hE' hS.gl,
    fun a b x y => hS.unit a b (ι x) (ι y), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨T, hf, hx, hs⟩ := (hmem _).1 x.2
    have hTD := hT T hf hs
    have hTS : T ≤ S := hTD.trans hDS
    have f1 : FiniteDimensional ℂ (T.comap S.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
    have f2 : FiniteDimensional ℂ (T.comap D.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTD).symm.finiteDimensional
    have hk : KStab ε E (T.comap S.subtype) := by
      rw [h4 n ε H σ S E hσ hS _ f1, Submodule.map_comap_subtype, inf_eq_right.2 hTS]
      exact hs
    exact ⟨T.comap D.subtype, f2, fun a b hab v hv => hk a b hab (ι v) hv, hx⟩
  · intro μ T hty
    have hTD := hT T hty.1 hty.2.1
    obtain ⟨v, hv0, hvT, hv⟩ := h5 n ε H σ S E hσ hS μ T hty (hTD.trans hDS)
    refine ⟨⟨v, hTD hvT⟩, fun h => hv0 (Subtype.ext (congrArg (fun z : D => (z : H)) h)), hvT, ?_⟩
    exact (kHighest_iff ε ι hι E' E hE' μ _).2 hv
  · intro μ x hx0 hx
    exact h6 n ε H σ S E hσ hS μ (ι x) (fun h => hx0 (hι (h.trans (map_zero ι).symm))) ((hmem _).1 x.2)
      ((kHighest_iff ε ι hι E' E hE' μ _).1 hx)
end GlobalTheory.CompanionTheory.KModExists
