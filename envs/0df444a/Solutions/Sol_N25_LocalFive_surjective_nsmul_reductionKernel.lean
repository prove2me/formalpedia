-- Prove2me | solution 1 for N25.LocalFive.surjective_nsmul_reductionKernel
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:25.006112+00:00
-- url     : https://prove2.me/submissions/8dd77179-6ab4-498d-84b1-b6e1e643d861

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Theorems.Thm_N25_LocalFive_henselian_R5
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open GoodReductionJacobian NeronModelInfra GoodReductionJacobian.RelativeGroupLaw

noncomputable section

local instance instL_N25_LocalFive_surjective_nsmul_reduction_bfd51b_s8a6835 : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

private theorem nsmul_changeSource
    {R : Type} [CommRing R] {A T : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (n : ℕ)
    (x : SchemeHomOver t f) :
    (G.nsmul t' n ⟨x.1, x.2.trans h⟩).1 = (G.nsmul t n x).1 := by
  subst t'
  rfl

/-- Henselian division with identity residue remains within the reduction kernel. -/
theorem _root_.solution
    {N : Scheme.{0}} {g : N ⟶ Spec (CommRingCat.of R5)}
    (L : RelativeGroupLaw R5 g) (hc : L.IsCommutative)
    (hsm : Smooth g) (n : ℕ) (hn : IsUnit (n : R5)) :
    Function.Surjective (fun u : reductionKernel L hc => n • u) := by
  letI : HenselianLocalRing R5 := henselian_R5
  letI : Smooth g := hsm
  obtain ⟨d, hd⟩ := L.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  letI : SmoothOfRelativeDimension d g := hd
  intro u
  have hi : Spec.map (CommRingCat.ofHom (algebraMap R5 R5)) =
      (𝟙 (Spec (CommRingCat.of R5))) := by
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R5))) g :=
    ⟨(AlgPoints.toPoint (u : L.AlgPoints hc R5)).1,
      (AlgPoints.toPoint (u : L.AlgPoints hc R5)).2.trans hi⟩
  have hred : GoodReductionJacobian.schemeHomOverComp
      (Spec.map (CommRingCat.ofHom (algebraMap R5 k5))) (Category.comp_id _) x =
        L.one (Spec.map (CommRingCat.ofHom (algebraMap R5 k5))) := by
    apply Subtype.ext
    have hu := congrArg (fun z : L.AlgPoints hc k5 => (AlgPoints.toPoint z).1) u.2
    change Spec.map (CommRingCat.ofHom (algebraMap R5 k5)) ≫
      (AlgPoints.toPoint (u : L.AlgPoints hc R5)).1 = (L.one _).1 at hu
    exact hu
  have hdiv : L.nsmul _ n (L.one (Spec.map (CommRingCat.ofHom (algebraMap R5 k5)))) =
      GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap R5 k5))) (Category.comp_id _) x := by
    rw [hred]
    exact L.nsmul_unit _ n
  obtain ⟨y, hyred, hyn⟩ :=
    L.exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing hc d n hn x _ hdiv
  let z : L.AlgPoints hc R5 := AlgPoints.ofPoint ⟨y.1, y.2.trans hi.symm⟩
  have hz : z ∈ reductionKernel L hc := by
    change reductionHom L hc z = 0
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom (algebraMap R5 k5)) ≫ y.1 = (L.one _).1
    exact congrArg Subtype.val hyred
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  change n • z = (u : L.AlgPoints hc R5)
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [AlgPoints.toPoint_nsmul]
  exact (nsmul_changeSource L hi.symm n y).trans (congrArg Subtype.val hyn)

end N25.LocalFive
