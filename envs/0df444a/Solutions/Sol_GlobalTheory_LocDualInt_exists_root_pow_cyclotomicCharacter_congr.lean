-- Prove2me | solution 1 for GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:53.332807+00:00
-- url     : https://prove2.me/submissions/b57e53d9-73d4-40dc-b062-882b72a96f1b

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterCongrRootOfUnityPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
open GlobalTheory GlobalTheory.LocDualInt
namespace GlobalTheory.LocDualInt
theorem _root_.solution {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ) :
    ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) =
      PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
        (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  classical
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity (PadicAlgCl p) (p ^ i) := fun i => by
    haveI : NeZero ((p ^ i : ℕ) : PadicAlgCl p) :=
      ⟨by exact_mod_cast pow_ne_zero i (Fact.out : p.Prime).ne_zero⟩
    infer_instance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  refine ⟨ζ, hζ.pow_eq_one, fun a ha => ?_⟩
  set c : ZMod (p ^ k) := PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have hspec := cyclotomicCharacter.spec (L := PadicAlgCl p) p
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have hg : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [hg, ha] at hspec
  have hpos : 0 < p ^ k := pow_pos (Fact.out : p.Prime).pos k
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, hpos, hζ.pow_eq_one⟩
  have hmod : a ≡ c.val [MOD orderOf ζ] := hfin.pow_eq_pow_iff_modEq.mp hspec
  rw [← hζ.eq_orderOf] at hmod
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod).trans (ZMod.natCast_zmod_val c)
end GlobalTheory.LocDualInt
