-- Prove2me | solution 1 for NumberField.PlaceDecomp.isCyclic_decomp_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/658a1c79-e198-51cb-b0c2-5f136312316f

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_NumberField_PlaceDecomp_decomp_eq_one_of_ramificationIdx_eq_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one

set_option autoImplicit false
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one.NumberField.PlaceDecomp"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one.NumberField CategoryTheory"

namespace NumberField
p2m_export "NumberField" "PlaceDecomp.decomp PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp decomp_eq_one_of_ramificationIdx_eq_one"
namespace Ws25B1h
p2m_open "NumberField.PlaceDecomp NumberField"

noncomputable def algEquivOfRingEquiv {k : Type} [Field k] (p : ℕ) [NeZero p] [CharP k p] (f : k ≃+* k) :
    letI := ZMod.algebra k p
    k ≃ₐ[ZMod p] k :=
  letI := ZMod.algebra k p
  AlgEquiv.ofRingEquiv (f := f) (fun x => by
    have hx : (algebraMap (ZMod p) k) x = ((x.val : ℕ) : k) := by
      rw [Algebra.algebraMap_eq_smul_one]
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [Nat.cast_smul_eq_nsmul, nsmul_one]
    rw [hx, map_natCast])

theorem algEquivOfRingEquiv_apply {k : Type} [Field k] (p : ℕ) [NeZero p] [CharP k p] (f : k ≃+* k) (x : k) :
    algEquivOfRingEquiv p f x = f x := rfl

theorem isCyclic_of_faithful_on_finiteField {G k : Type} [Group G] [Field k] [Finite k] [MulSemiringAction G k]
    (h : ∀ g : G, (∀ z : k, g • z = z) → g = 1) : IsCyclic G := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite k p⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos k p
  letI := ZMod.algebra k p

  obtain ⟨φ, hφ⟩ : ∃ φ : G →* (k ≃ₐ[ZMod p] k), ∀ (g : G) (z : k), φ g z = g • z :=
    ⟨{ toFun := fun g => algEquivOfRingEquiv p (MulSemiringAction.toRingEquiv G k g)
       map_one' := by ext z; rw [algEquivOfRingEquiv_apply]; exact one_smul G z
       map_mul' := fun g g' => by ext z; exact mul_smul g g' z }, fun _ _ => rfl⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact h g (fun z => by rw [← hφ, hg]; rfl)
  haveI : IsCyclic (φ.range) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom (MonoidHom.ofInjective hinj).symm.surjective

end NumberField.PlaceDecomp.Ws25B1h

open NumberField.PlaceDecomp.Ws25B1h in
theorem solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    IsCyclic (NumberField.PlaceDecomp.decomp E K w) := by
  classical
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers K)) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K w
  refine isCyclic_of_faithful_on_finiteField (k := IsLocalRing.ResidueField (w.adicCompletionIntegers K)) (fun σ hσ => ?_)
  refine NumberField.PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one E K w hw σ (fun a => ?_)
  have h : IsLocalRing.residue (w.adicCompletionIntegers K) (σ • a) = IsLocalRing.residue (w.adicCompletionIntegers K) a := by
    rw [IsLocalRing.ResidueField.residue_smul]
    exact hσ _
  exact (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))).mp h

end S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one (solution)
