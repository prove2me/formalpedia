-- Prove2me | solution 1 for GlobalTheory.DvrModel.sec_eq_zero_of_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:22.207262+00:00
-- url     : https://prove2.me/submissions/fa053295-7d7c-416b-a5bb-db0a45a81f02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_PrimeSection_eq_zero_of_forall_pow_dvd_germ
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
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
    (h : ∀ a (n : ℕ), s.f a ∈
      Ideal.span {H.presheaf.map (homOfLE (le_top : L.U a ≤ ⊤)).op cst[f, V, ϖ]} ^ n)
    (a : L.ι) : s.f a = 0 := by
  have := isIntegral hK
  have := isLocallyNoetherian f
  obtain ⟨b, hb⟩ := LB.mem_of_cover hL (i (genericPoint Hs))
  refine eq_zero_of_forall_pow_dvd_germ (fun a b ↦ L.g a b) s.f s.compat hb
    ((notMem_basicOpen_iff_specializes hϖ hs _).2 specializes_rfl) (fun n ↦ ?_) a
  have := h b n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  have := map_dvd (H.presheaf.germ _ _ hb).hom this
  rwa [map_pow, germ_res] at this
end GlobalTheory.DvrModel
