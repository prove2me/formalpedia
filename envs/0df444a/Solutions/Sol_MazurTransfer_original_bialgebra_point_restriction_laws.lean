-- Prove2me | solution 1 for MazurTransfer.original_bialgebra_point_restriction_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:53:16.145499+00:00
-- url     : https://prove2.me/submissions/6c609d60-3b4b-49de-ba1d-df3c6343bc4e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original bialgebra inclusion induces its exact multiplicative point restriction over every original coefficient algebra.
Named downstream consumer: actual integral norm-kernel character quotients and their torsor cocycles.
-/
import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
noncomputable section

open MazurTransfer.BialgebraPointRestriction
universe u
namespace MazurTransfer.OriginalBialgebraPointRestrictionProof20261020Boundary
end MazurTransfer.OriginalBialgebraPointRestrictionProof20261020Boundary
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine bialgebra inclusion induces multiplicative
point restriction over EVERY coefficient algebra, naturally under every
coefficient map. Named downstream consumer: actual integral norm-kernel
character quotients and their torsor cocycles.
-/

noncomputable section
namespace MazurTransfer.OriginalBialgebraPointRestrictionProof20261020
variable {R H G : Type u} [CommRing R] [CommRing H] [CommRing G]
variable [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G)



theorem restrictPoint_mul {T : Type u} [CommRing T] [Algebra R T]
    (f g : WithConv (G →ₐ[R] T)) :
    restrictPoint ι (f * g) = restrictPoint ι f * restrictPoint ι g :=
  congrArg WithConv.toConv (AlgHom.convMul_comp_bialgHom_distrib f g ι)

theorem restrictPoint_one {T : Type u} [CommRing T] [Algebra R T] :
    restrictPoint ι (1 : WithConv (G →ₐ[R] T)) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  change algebraMap R T (Coalgebra.counit (R := R) (ι x)) =
    algebraMap R T (Coalgebra.counit (R := R) x)
  exact congrArg (algebraMap R T) (LinearMap.congr_fun (CoalgHomClass.counit_comp ι) x)

theorem restrictPoint_natural {T T' : Type u} [CommRing T] [Algebra R T]
    [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)) :
    restrictPoint ι (.toConv (g.comp f.ofConv)) =
      WithConv.toConv (g.comp (restrictPoint ι f).ofConv) := rfl

end MazurTransfer.OriginalBialgebraPointRestrictionProof20261020

theorem solution : (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T : Type u} [CommRing T] [Algebra R T]
    (f g : WithConv (G →ₐ[R] T)),
restrictPoint ι (f * g) = restrictPoint ι f * restrictPoint ι g) ∧ (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T : Type u} [CommRing T] [Algebra R T],
restrictPoint ι (1 : WithConv (G →ₐ[R] T)) = 1) ∧ (∀ {R H G : Type u} [CommRing R] [CommRing H] [CommRing G] [Bialgebra R H] [Bialgebra R G] (ι : H →ₐc[R] G), ∀ {T T' : Type u} [CommRing T] [Algebra R T]
    [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)),
restrictPoint ι (.toConv (g.comp f.ofConv)) =
      WithConv.toConv (g.comp (restrictPoint ι f).ofConv)) := by
  exact ⟨MazurTransfer.OriginalBialgebraPointRestrictionProof20261020.restrictPoint_mul, MazurTransfer.OriginalBialgebraPointRestrictionProof20261020.restrictPoint_one, MazurTransfer.OriginalBialgebraPointRestrictionProof20261020.restrictPoint_natural⟩
#print axioms solution
