-- Prove2me | solution 1 for GroundTheory.Global.Artin.zpowers_arithFrob_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:36.598061+00:00
-- url     : https://prove2.me/submissions/d9c60917-e990-4ea2-96a0-d349cdfd1db5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
import Definitions.Def_GroundTheory_GlobalFields_Artin_InductionFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open NumberField IsDedekindDomain
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
namespace GroundTheory.Global.Artin
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    Subgroup.zpowers ((⟨φ, hφ.mem_stabilizer⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
      MulAction.stabilizer Gal(L/K) w.asIdeal ⧸
        (w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)) =
      ⊤ := by
  classical
  set Q := w.asIdeal with hQ
  set P := Q.under (𝓞 K) with hP
  have : Q.IsMaximal := w.isMaximal
  have : P.IsMaximal := by rw [hP]; infer_instance
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have : Finite (𝓞 K ⧸ P) := hφ.finite_quotient
  have := Fintype.ofFinite (𝓞 K ⧸ P)
  have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q w.ne_bot
  set e := Ideal.Quotient.stabilizerHom Q P Gal(L/K)
  have hfrob : e ⟨φ, hφ.mem_stabilizer⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ P) (𝓞 L ⧸ Q) := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    change Ideal.Quotient.mk Q (φ • y) = Ideal.Quotient.mk Q y ^ Fintype.card (𝓞 K ⧸ P)
    rw [← Nat.card_eq_fintype_card]
    exact hφ.mk_apply y
  rw [eq_top_iff]
  rintro c -
  induction c using QuotientGroup.induction_on with | H d => ?_
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 K ⧸ P) (𝓞 L ⧸ Q)).2 (e d)
  refine Subgroup.mem_zpowers_iff.2 ⟨(n.1 : ℤ), ?_⟩
  have hk : ((⟨φ, hφ.mem_stabilizer⟩ : MulAction.stabilizer Gal(L/K) Q) ^ n.1)⁻¹ * d ∈ e.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hfrob, ← hn, inv_mul_cancel]
  rw [Ideal.Quotient.ker_stabilizerHom, ← Ideal.coe_mem_inertia] at hk
  rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact hk
end GroundTheory.Global.Artin
