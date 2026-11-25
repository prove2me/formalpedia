-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.eq_of_natCast_mem_rootsOfUnityField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:52.589362+00:00
-- url     : https://prove2.me/submissions/e79f568c-8809-4d93-a5d9-32c4262a62fa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (k : ℕ)
    {Q₁ Q₂ : Ideal (𝓞 (rootsOfUnityField (p ^ (k + 1))))} [Q₁.IsPrime] [Q₂.IsPrime]
    (h₁ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₁)
    (h₂ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₂) : Q₁ = Q₂ := by
  let L := rootsOfUnityField (p ^ (k + 1))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ (p ^ (k + 1))
  let ζL : L := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
  have hζL : IsPrimitiveRoot ζL (p ^ (k + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L ℚ̄) hζ (algebraMap L ℚ̄).injective
  have hprime : Prime (hζL.toInteger - 1) := hζL.zeta_sub_one_prime
  have hmax : (Ideal.span {hζL.toInteger - 1}).IsMaximal :=
    ((Ideal.span_singleton_prime hprime.ne_zero).2 hprime).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero)
  have key : ∀ Q : Ideal (𝓞 L), Q.IsPrime → (p : 𝓞 L) ∈ Q →
      Q = Ideal.span {hζL.toInteger - 1} := by
    intro Q hQ hpQ
    refine (hmax.eq_of_le hQ.ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    have : CharP (𝓞 L ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hpQ)
    have h1 : (Ideal.Quotient.mk Q (hζL.toInteger - 1)) ^ (p ^ (k + 1)) = 0 := by
      rw [map_sub, map_one, sub_pow_char_pow, ← map_pow,
        (hζL.toInteger_isPrimitiveRoot).pow_eq_one, map_one, one_pow, sub_self]
    exact (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).1 h1
  rw [key Q₁ ‹_› h₁, key Q₂ ‹_› h₂]
end GroundTheory.Global.Cyclotomic
