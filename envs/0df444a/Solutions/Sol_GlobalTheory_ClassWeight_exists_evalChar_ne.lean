-- Prove2me | solution 1 for GlobalTheory.ClassWeight.exists_evalChar_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:54.713488+00:00
-- url     : https://prove2.me/submissions/6cc929b8-4239-4a00-91f7-18ca3935f0fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
import Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
namespace GlobalTheory.ClassWeight
theorem _root_.solution [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) {α β : X}
    (h : ¬ ∃ mu, β = α + N • mu) : ∃ τ : TorChar X F N, evalChar F N β τ ≠ evalChar F N α τ := by
  have : NeZero (N : F) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have : NeZero N := ⟨hN0⟩
  let K : AddSubgroup X := (nsmulAddMonoidHom N : X →+ X).range
  have hK : ∀ q : X ⧸ K, N • q = 0 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨x, rfl⟩
  have : Module.Finite ℤ (X ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap (QuotientAddGroup.mk'_surjective K)
  have : Finite (X ⧸ K) := Module.finite_of_fg_torsion _ fun q =>
    ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, (natCast_zsmul q N).trans (hK q)⟩
  have h0 : HasEnoughRootsOfUnity F N := inferInstance
  have : HasEnoughRootsOfUnity F (Monoid.exponent (Multiplicative (X ⧸ K))) :=
    h0.of_dvd F (Monoid.exponent_dvd_of_forall_pow_eq_one fun q => hK q.toAdd)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative (X ⧸ K)) F
    (a := Multiplicative.ofAdd ((β - α : X) : X ⧸ K)) fun e => by
      obtain ⟨mu, hmu⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((β - α : X) : X ⧸ K) = 0 from e)
      exact h ⟨mu, (sub_eq_iff_eq_add'.1 hmu.symm)⟩
  let τ : TorChar X F N := ⟨φ.comp (QuotientAddGroup.mk' K).toMultiplicative, MonoidHom.ext fun x =>
    (map_pow φ _ N).symm.trans ((congrArg φ (show (Multiplicative.ofAdd (x.toAdd : X ⧸ K)) ^ N = 1 from hK (x.toAdd : X ⧸ K))).trans (map_one φ))⟩
  refine ⟨τ, fun e => hφ ?_⟩
  have e₂ := evalChar_add (β - α) α τ
  rw [sub_add_cancel, e] at e₂
  exact right_eq_mul.1 e₂
end GlobalTheory.ClassWeight
