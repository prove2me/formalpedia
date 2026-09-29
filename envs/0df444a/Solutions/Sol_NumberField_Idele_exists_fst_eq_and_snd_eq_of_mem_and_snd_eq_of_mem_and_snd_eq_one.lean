-- Prove2me | solution 1 for NumberField.Idele.exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3fda6c82-82d8-5c24-b20b-738a30ad23a2

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace IdeleSplice

variable (K : Type) [Field K] [NumberField K]

noncomputable def bump (a : HeightOneSpectrum (𝓞 K)) (t : (a.adicCompletion K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 K) K) (AdelicLevel.localUnit (𝓞 K) K a t)

theorem bump_fst (a : HeightOneSpectrum (𝓞 K)) (t : (a.adicCompletion K)ˣ) :
    ((bump K a t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem bump_snd_self (a : HeightOneSpectrum (𝓞 K)) (t : (a.adicCompletion K)ˣ) :
    ((bump K a t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 a = t := by
  show ((AdelicLevel.localUnit (𝓞 K) K a t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) a = t
  exact AdelicLevel.localUnit_apply_self (𝓞 K) K a t

theorem bump_snd_of_ne (a : HeightOneSpectrum (𝓞 K)) (t : (a.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ a) :
    ((bump K a t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  show ((AdelicLevel.localUnit (𝓞 K) K a t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact AdelicLevel.localUnit_apply_of_ne (𝓞 K) K a t hw

theorem mul_fst (y u : (AdeleRing (𝓞 K) K)ˣ) :
    ((y * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (y : AdeleRing (𝓞 K) K).1 * (u : AdeleRing (𝓞 K) K).1 := rfl

theorem mul_snd_apply (y u : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((y * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = (y : AdeleRing (𝓞 K) K).2 w * (u : AdeleRing (𝓞 K) K).2 w := rfl

end IdeleSplice

open IdeleSplice in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) :
    ∃ zs : (AdeleRing (𝓞 K) K)ˣ,
      ((zs : AdeleRing (𝓞 K) K).1 = (z : AdeleRing (𝓞 K) K).1) ∧
      (∀ v ∈ S, (zs : AdeleRing (𝓞 K) K).2 v = (z : AdeleRing (𝓞 K) K).2 v) ∧
      (∀ v ∈ T, v ∉ S → (zs : AdeleRing (𝓞 K) K).2 v = ((x v : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → (zs : AdeleRing (𝓞 K) K).2 v = 1) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨NumberField.Idele.partAt K S z, NumberField.Idele.partAt_fst K S z,
      fun v hv => NumberField.Idele.partAt_snd_of_mem K S z hv, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v hvS _ => NumberField.Idele.partAt_snd_of_not_mem K S z hvS⟩
  | insert a T haT ih =>
    obtain ⟨zs, h1, hS, hT, h0⟩ := ih
    by_cases haS : a ∈ S
    · refine ⟨zs, h1, hS, fun v hv hvS => ?_, fun v hvS hvT => ?_⟩
      · rcases Finset.mem_insert.1 hv with rfl | hv'
        · exact absurd haS hvS
        · exact hT v hv' hvS
      · exact h0 v hvS fun h => hvT (Finset.mem_insert_of_mem h)
    · refine ⟨zs * bump K a (x a), ?_, fun v hv => ?_, fun v hv hvS => ?_, fun v hvS hvT => ?_⟩
      · rw [mul_fst, bump_fst, mul_one, h1]
      · have hva : v ≠ a := fun h => haS (h ▸ hv)
        rw [mul_snd_apply, bump_snd_of_ne K a (x a) hva, mul_one, hS v hv]
      · rcases Finset.mem_insert.1 hv with rfl | hv'
        · rw [mul_snd_apply, bump_snd_self, h0 v hvS haT, one_mul]
        · have hva : v ≠ a := fun h => haT (h ▸ hv')
          rw [mul_snd_apply, bump_snd_of_ne K a (x a) hva, mul_one, hT v hv' hvS]
      · have hva : v ≠ a := fun h => hvT (h ▸ Finset.mem_insert_self a T)
        rw [mul_snd_apply, bump_snd_of_ne K a (x a) hva, mul_one,
          h0 v hvS fun h => hvT (Finset.mem_insert_of_mem h)]

end S_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
end P2MW
export P2MW.S_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one (solution)
