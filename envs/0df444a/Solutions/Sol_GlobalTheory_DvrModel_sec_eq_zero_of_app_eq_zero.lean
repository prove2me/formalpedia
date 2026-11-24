-- Prove2me | solution 1 for GlobalTheory.DvrModel.sec_eq_zero_of_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:10.368001+00:00
-- url     : https://prove2.me/submissions/bb3cd209-a51a-48ca-9dd3-f596f2749b33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_PrimeSection_eq_zero_of_forall_pow_dvd_germ
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_ker_app_eq_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))
include hK hs
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB) (s : L.Sec)
    {Z : ℕ → Scheme.{u}} {k : ∀ n, Z n ⟶ H}
    {p : ∀ n, Z n ⟶ Spec (.of (V ⧸ Ideal.span {ϖ ^ n}))}
    (hZ : ∀ n, IsPullback (k n) (p n) f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})))))
    (h : ∀ a n, (k n).app (L.U a) (s.f a) = 0) (a : L.ι) : s.f a = 0 := by
  have := isIntegral hK
  have := isLocallyNoetherian f
  obtain ⟨b, hb⟩ := LB.mem_of_cover hL (i (genericPoint Hs))
  refine eq_zero_of_forall_pow_dvd_germ (fun a b ↦ L.g a b) s.f s.compat hb
    ((notMem_basicOpen_iff_specializes hϖ hs _).2 specializes_rfl) (fun n ↦ ?_) a
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset hb
  have hAU : A ≤ L.U b := hAU
  have hm : H.presheaf.map (homOfLE hAU).op (s.f b) ∈ RingHom.ker ((k n).app A).hom := by
    change (k n).app A _ = 0
    rw [← ConcreteCategory.comp_apply, (k n).naturality, ConcreteCategory.comp_apply, h, map_zero]
  rw [ker_app_eq_span (β := CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})))
    Ideal.Quotient.mk_surjective Ideal.mk_ker (hZ n) hA, Ideal.mem_span_singleton] at hm
  have := map_dvd (H.presheaf.germ _ _ hxA).hom hm
  rwa [germ_res, germ_res, map_pow, map_pow, map_pow] at this
end GlobalTheory.DvrModel
