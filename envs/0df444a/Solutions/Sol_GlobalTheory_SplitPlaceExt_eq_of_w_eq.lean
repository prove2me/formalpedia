-- Prove2me | solution 1 for GlobalTheory.SplitPlaceExt.eq_of_w_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:22:27.384844+00:00
-- url     : https://prove2.me/submissions/fe52b637-8691-4b41-89ea-3e68346c435c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgHomEqOrConj
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep
import Theorems.Thm_ReciprocityTheory_Aut_SplitPlace_w_under


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.SplitPlaceExt
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
open NumberField IsDedekindDomain
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
namespace GlobalTheory.SplitPlaceExt
namespace _root_.GlobalTheory.SplitPlaceExt
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : _root_.ReciprocityTheory.Aut.SplitPlace L), s'.w = s.w → s' = s := by
  intro L _ _ _ s s' h
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain rfl : v = v' := hv.symm
  have key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1 := fun x =>
    Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.SplitSep.exists_sep L ⟨v, i⟩
  set c := i.comp (IsCMField.complexConj L).toAlgHom with hc
  have hce : c e = i (IsCMField.complexConj L e) := rfl
  have hic : i ≠ c := by
    intro hi
    have : Valued.v (i e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 this.ne
  have hi'c : i' ≠ c := by
    intro hi
    have : Valued.v (i' e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 ((key e).1 this).ne
  by_contra hne
  have hii' : i' ≠ i := fun hh => hne (by rw [hh])
  have hinj : Function.Injective ![i, c, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h3 : Nat.card (Fin 3) ≤ _ := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  have h2 := card_algHom_le_finrank (maximalRealSubfield L) L
    (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  omega
end _root_.GlobalTheory.SplitPlaceExt
end GlobalTheory.SplitPlaceExt
