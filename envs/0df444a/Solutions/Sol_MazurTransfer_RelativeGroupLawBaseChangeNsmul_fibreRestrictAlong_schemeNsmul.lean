-- Prove2me | solution 1 for MazurTransfer.RelativeGroupLawBaseChangeNsmul.fibreRestrictAlong_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T04:41:55.390907+00:00
-- url     : https://prove2.me/submissions/d12c8656-18aa-4fc5-bc37-3d6bbf53f5ca

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: scalar multiplication for the existing relative group
law commutes with arbitrary base change, on points and scheme morphisms.
Named downstream consumer: identify the SAME integral order-13 norm
composite with local multiplication by nineteen.
-/
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian NeronSpecialFibreInfra
namespace MazurTransfer.RelativeGroupLawBaseChangeNsmulProofHelpers20261018
variable {R R' : Type u} [CommRing R] [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem baseChangePointToBase_nsmul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t (pullback.snd f ι)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t n x) =
      G.nsmul (t ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι G t
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
        RelativeGroupLaw.baseChangePointToBase_mul, ih]

end MazurTransfer.RelativeGroupLawBaseChangeNsmulProofHelpers20261018
open MazurTransfer.RelativeGroupLawBaseChangeNsmulProofHelpers20261018

theorem solution {R R' : Type u} [CommRing R] [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    fibreRestrictAlong ι f f ⟨G.schemeNsmul n, G.schemeNsmul_over n⟩ =
      ⟨(G.baseChange ι).schemeNsmul n, (G.baseChange ι).schemeNsmul_over n⟩ := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [fibreRestrictAlong_coe_comp_fst]
    have h := congrArg Subtype.val (baseChangePointToBase_nsmul ι G
      (pullback.snd f ι) n RelativeGroupLaw.idPoint)
    change (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι =
      (G.nsmul (pullback.snd f ι ≫ ι) n
        (RelativeGroupLaw.baseChangePointToBase ι RelativeGroupLaw.idPoint)).val at h
    rw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul] at h
    change _ = (𝟙 _ ≫ pullback.fst f ι) ≫ G.schemeNsmul n at h
    rw [Category.id_comp] at h
    exact h.symm
  · rw [fibreRestrictAlong_coe_comp_snd]
    exact ((G.baseChange ι).schemeNsmul_over n).symm

#print axioms solution
