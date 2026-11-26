-- Prove2me | solution 1 for KrohnRhodes.dks_aux_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:49.047654+00:00
-- url     : https://prove2.me/submissions/2540d04a-bf2a-41b9-a45e-143dc4d9268f

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
public import Theorems.Thm_KrohnRhodes_reset_submonoid_aperiodic
public import Theorems.Thm_KrohnRhodes_group_decomposition
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_group_subquotient_faithful_aux
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
public import Theorems.Thm_divTowerWreath_ofAperiodic
public import Theorems.Thm_divTowerWreath_wreathStep
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {Q M : Type} [Fintype Q] [Monoid M] [Finite M]
    (act : M →* Function.End Q) (_hU : ∀ m : M, IsUnit m) :
    ∃ factors : List KRFactor.{0}, DivTowerWreath ↥(closureMonoid act) factors ∧
      ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
        KrohnRhodes.MonoidDivides F.carrier M := by
  classical
  -- Endow `M` with its group structure (definitionally extending the given monoid).
  let : Group M := groupOfIsUnit _hU
  have : Fintype M := Fintype.ofFinite M
  -- The group-case decomposition: the closure divides `U(Q) ≀_M M`.
  have hdec : SgDiv ↥(closureMonoid act) (WreathProduct ↥(resetSubmonoid Q) M M) :=
    group_decomposition act
  -- The base tower: the subquotient-faithful group tower for `M`, every factor
  -- (in particular every simple-group factor) dividing `M`.
  obtain ⟨towB⟩ := KrohnRhodes.group_subquotient_faithful_aux (Nat.card M) M le_rfl
  -- Assemble: factors := reset atom :: group tower.
  refine ⟨KRFactor.ofAperiodic ↥(resetSubmonoid Q) (reset_submonoid_aperiodic Q)
      :: towB.factors, ?_, ?_⟩
  · -- `divTowerWreath_wreathStep` concatenates the one-rung reset tower with the
    -- group tower along the division `hdec`.
    exact divTowerWreath_wreathStep
      [KRFactor.ofAperiodic ↥(resetSubmonoid Q) (reset_submonoid_aperiodic Q)]
      hdec (divTowerWreath_ofAperiodic _ (reset_submonoid_aperiodic Q)) towB.divides
  · -- The head atom is aperiodic-flagged (kind mismatch is impossible); the tail's
    -- simple-group factors divide `M` by the tower's `factorsDivide` field.
    intro F hF hk
    rcases List.mem_cons.mp hF with rfl | hF'
    · simp at hk
    · exact towB.factorsDivide F hF'
end KrohnRhodes
