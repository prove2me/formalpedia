-- Prove2me | solution 1 for MasulloGRH.s_idele_class_group_open_embedding
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:42:08.638485+00:00
-- url     : https://prove2.me/submissions/07d88ffe-4df8-47dd-92d0-dd7a656cfcf3

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles
import Theorems.Thm_MasulloGRH_idele_class_group_topology

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_s_idele_class_group_open_embedding

open MasulloGRH

/-- For an open subgroup `U` and a normal subgroup `P` of a topological group `G`, the natural
homomorphism `U ⧸ (U ∩ P) → G ⧸ P` is an open embedding. -/
theorem isOpenEmbedding_quotient_map_subtype {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U P : Subgroup G) [P.Normal] (hU : IsOpen (U : Set G)) :
    Topology.IsOpenEmbedding
      (QuotientGroup.map (P.subgroupOf U) P U.subtype le_rfl) := by
  have hqU : IsOpenQuotientMap (QuotientGroup.mk : U → U ⧸ P.subgroupOf U) :=
    QuotientGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap (QuotientGroup.mk : G → G ⧸ P) :=
    QuotientGroup.isOpenQuotientMap_mk
  have hcomp : (QuotientGroup.map (P.subgroupOf U) P U.subtype le_rfl) ∘
      (QuotientGroup.mk : U → U ⧸ P.subgroupOf U) =
      (QuotientGroup.mk : G → G ⧸ P) ∘ (Subtype.val : U → G) := rfl
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · refine hqU.continuous_comp_iff.mp ?_
    rw [hcomp]
    exact hq.continuous.comp continuous_subtype_val
  · rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro c hc
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
    have h1 : (QuotientGroup.mk (u : G) : G ⧸ P) = 1 := hc
    rw [QuotientGroup.eq_one_iff] at h1 ⊢
    exact h1
  · refine hqU.isOpenMap_iff.mpr ?_
    rw [hcomp]
    exact hq.isOpenMap.comp hU.isOpenMap_subtype_val

variable {F : Type*} [Field F] [NumberField F]

/-- The group `J_S` of ideles that are units at every finite place outside `S`. -/
def sIdeleSubgroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (IdeleGroup F) where
  carrier := sIntegralIdeles Sf
  mul_mem' := by
    intro g h hg hh v hv
    show Valued.v ((g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v) = 1
    rw [map_mul, hg v hv, hh v hv, one_mul]
  one_mem' := by
    intro v _
    show Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  inv_mem' := by
    intro g hg v hv
    have h1 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v * (g : AdeleRing (𝓞 F) F).2 v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) g.inv_mul
    have h2 := congrArg (Valued.v : v.adicCompletion F → _) h1
    rw [map_mul, hg v hv, mul_one, map_one] at h2
    exact h2

theorem coe_sIdeleSubgroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    (sIdeleSubgroup Sf : Set (IdeleGroup F)) = sIntegralIdeles Sf := rfl

/-- The ideles that are units at every finite place form a neighbourhood of `1` contained in
`J_S`; hence `J_S` is open. -/
theorem isOpen_sIdeleSubgroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (sIdeleSubgroup Sf : Set (IdeleGroup F)) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hc1 : Continuous fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_val
  have hc2 : Continuous fun g : IdeleGroup F => ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hW : IsOpen ({g : IdeleGroup F |
      (∀ v, (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v, ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)}) :=
    (hO.preimage hc1).inter (hO.preimage hc2)
  refine Subgroup.isOpen_of_mem_nhds (sIdeleSubgroup Sf) (g := 1)
    (Filter.mem_of_superset (hW.mem_nhds ?_) ?_)
  · refine ⟨fun v => ?_, fun v => ?_⟩
    · show (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact one_mem _
    · rw [inv_one]
      show (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact one_mem _
  · rintro g ⟨hg, hg'⟩ v _
    have h1 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v * (g : AdeleRing (𝓞 F) F).2 v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) g.inv_mul
    have h2 := congrArg (Valued.v : v.adicCompletion F → _) h1
    rw [map_mul, map_one] at h2
    have ha := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (hg v)
    have hb := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (hg' v)
    exact eq_one_of_one_le_mul_left ha hb (by rw [mul_comm]; exact h2.ge)

/-- A principal idele lies in `J_S` exactly when it comes from an `S`-unit. -/
theorem principalIdele_mem_sIdeleSubgroup (Sf : Finset (HeightOneSpectrum (𝓞 F))) (ξ : Fˣ) :
    principalIdele F ξ ∈ sIdeleSubgroup Sf ↔ ξ ∈ SUnits Sf := by
  show (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
      Valued.v (((ξ : F) : v.adicCompletion F)) = 1) ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (Sf : Set (HeightOneSpectrum (𝓞 F))) →
      v.valuation F (ξ : F) = 1
  refine forall_congr' fun v => ?_
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Finset.mem_coe]

end Sol_MasulloGRH_s_idele_class_group_open_embedding

open MasulloGRH Sol_MasulloGRH_s_idele_class_group_open_embedding

theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ U : Subgroup (IdeleGroup F),
      (U : Set (IdeleGroup F)) = sIntegralIdeles Sf ∧
      IsOpen (U : Set (IdeleGroup F)) ∧
      (∀ ξ : Fˣ, principalIdele F ξ ∈ U ↔ ξ ∈ SUnits Sf) ∧
      T2Space (U ⧸ (principalIdeles F).subgroupOf U) ∧
      LocallyCompactSpace (U ⧸ (principalIdeles F).subgroupOf U) ∧
      ∃ j : (U ⧸ (principalIdeles F).subgroupOf U) →* IdeleClassGroup F,
        Topology.IsOpenEmbedding j ∧
        (∀ u : U, j (QuotientGroup.mk u) = QuotientGroup.mk (u : IdeleGroup F)) ∧
        Set.range j = sIdeleClasses Sf := by
  obtain ⟨-, -, hT2, hLC, -⟩ := idele_class_group_topology F
  have hopen := isOpen_sIdeleSubgroup (F := F) Sf
  have hemb := isOpenEmbedding_quotient_map_subtype (sIdeleSubgroup Sf) (principalIdeles F) hopen
  refine ⟨sIdeleSubgroup Sf, coe_sIdeleSubgroup Sf, hopen,
    principalIdele_mem_sIdeleSubgroup Sf, hemb.isEmbedding.t2Space, hemb.locallyCompactSpace,
    QuotientGroup.map ((principalIdeles F).subgroupOf (sIdeleSubgroup Sf)) (principalIdeles F)
      (sIdeleSubgroup Sf).subtype le_rfl, hemb, fun u => rfl, ?_⟩
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨(u : IdeleGroup F), u.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk (⟨g, hg⟩ : sIdeleSubgroup Sf), rfl⟩
