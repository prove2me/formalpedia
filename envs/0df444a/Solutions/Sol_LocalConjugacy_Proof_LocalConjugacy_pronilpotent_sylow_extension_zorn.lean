-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_extension_zorn
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:28:25.825984+00:00
-- url     : https://prove2.me/submissions/75d0bc97-cb0a-4e97-aac8-442562e023ab

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_coprime_prime_index_restriction_locallyFinite
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_minimal_surjectivity_counterexample
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_prime_index_above_sylow
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_sylow_restriction_injective_zorn
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_normal_of_pronilpotent

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





private theorem invariant_iff_twist {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) :
    InvariantUnder (⊤ : Subgroup J) K f ↔ ∀ j : J, Cohomologous f (twistCocycle f j) := by
  constructor
  · intro h j
    obtain ⟨n, hn⟩ := h j (Subgroup.mem_top _)
    exact ⟨n, fun x => hn x x.property (conjugateDomain K j x).property⟩
  · intro h j _
    obtain ⟨n, hn⟩ := h j
    exact ⟨n, fun x hx _ => hn ⟨x, hx⟩⟩



private theorem restrict_twist {K L : Subgroup J} [K.Normal] [L.Normal]
    (hKL : K ≤ L) (f : Cocycle (N := N) L) (j : J) :
    restrictCocycle hKL (twistCocycle f j) = twistCocycle (restrictCocycle hKL f) j := by
  rfl



end General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false



end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Compactness
variable {J : Type*} [Group J] [TopologicalSpace J] [CompactSpace J]





end Compactness

section Extension
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]







end Extension

section Obstructions
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]











/-- The fixed-class Zorn induction principle. It assumes extension only for
this class on smaller subgroups, never full surjectivity on those subgroups. -/
private theorem extendsTo_of_zorn_step
    (P : Subgroup J) (f : Cocycle (N := N) P)
    (step : ∀ L : Subgroup J, IsClosed (L : Set J) → P < L →
      (∀ K : Subgroup J, IsClosed (K : Set J) → P ≤ K → K < L → f.ExtendsTo K) →
      f.ExtendsTo L) : f.ExtendsTo ⊤ := by
  classical
  by_contra hbad
  obtain ⟨L, hL, hPL, hf, hmin⟩ := exists_minimal_surjectivity_counterexample P f hbad
  exact hf (step L hL hPL hmin)



end Obstructions

section Invariance
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- After injectivity has been established, any lift of an ambient-invariant
class on a normal subgroup is itself ambient-invariant. Unlike Proposition
2.3, this step needs no surjectivity theorem for the intermediate subgroup. -/
private theorem invariant_lift_of_injective_restriction
    (L K : Subgroup J) [L.Normal] [K.Normal] (hKL : K ≤ L)
    (hinj : ∀ f g : Cocycle (N := N) L,
      Cohomologous (restrictCocycle hKL f) (restrictCocycle hKL g) → Cohomologous f g)
    (f : Cocycle (N := N) L) (g : Cocycle (N := N) K)
    (hg : InvariantUnder ⊤ K g) (hfg : RestrictsTo hKL f g) :
    InvariantUnder ⊤ L f := by
  rw [invariant_iff_twist]
  intro j
  apply hinj
  rw [restrict_twist]
  have hfg' : Cohomologous (restrictCocycle hKL f) g := hfg
  exact cohomologous_trans hfg' (cohomologous_trans
    ((invariant_iff_twist g).mp hg j)
    (cohomologous_symm (twist_cohomologous hfg' j)))

end Invariance
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

private theorem locallyFiniteGroup_of_finite (G : Type*) [Group G] [Finite G] :
    LocallyFiniteGroup G := fun _ _ => Set.toFinite _

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [CompactSpace J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



end

section Subgroup
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N]
  [MulDistribMulAction J N]
  (M : Subgroup N) (hM : ∀ (j : J) (n : N), n ∈ M → j • n ∈ M)





namespace Cocycle



end Cocycle
end Subgroup

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- A chosen Sylow subgroup remains Sylow in every intermediate subgroup. -/
private theorem isSylowPro_of_intermediate {J : Type*} [Group J] [TopologicalSpace J]
    {p : ℕ} {H L P : Subgroup J} (hP : IsSylowPro p H P)
    (hPL : P ≤ L) (hLH : L ≤ H) : IsSylowPro p L P :=
  ⟨hPL, hP.2.1, hP.2.2.1,
    fun Q hQL hQclosed hQpro hPQ => hP.2.2.2 Q (hQL.trans hLH) hQclosed hQpro hPQ⟩

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



/-- The last step in the Zorn proof of surjectivity: a lift to a normal
prime-index subgroup is ambient-invariant by the already proved injectivity,
and Proposition 2.2 then lifts it to the whole group. Full surjectivity on the
intermediate subgroup is not assumed. -/
private theorem extend_stable_class_across_prime_index [IsTopologicalGroup N]
    (hfinite : LocallyFiniteGroup N)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p) (hN : IsPGroup p N)
    (K P : Subgroup J) [K.Normal] [P.Normal] (hPK : P ≤ K)
    (hK : IsClosed (K : Set J)) (hindex : K.index = q)
    (hinj : ∀ f g : Cocycle (N := N) K,
      Cohomologous (restrictCocycle hPK f) (restrictCocycle hPK g) → Cohomologous f g)
    (f : Cocycle (N := N) P) (hf : InvariantUnder ⊤ P f)
    (hext : f.ExtendsTo K) : f.ExtendsTo ⊤ := by
  obtain ⟨_, g, hg⟩ := hext
  have hginv := invariant_lift_of_injective_restriction K P hPK hinj g f hf hg
  obtain ⟨F, hF⟩ := (coprime_prime_index_restriction_locallyFinite
    hfinite hne hN K hK hindex).2 g hginv
  refine ⟨le_top, F, ?_⟩
  have hFg : Cohomologous (restrictCocycle (show K ≤ ⊤ from le_top) F) g := hF
  have hgf : Cohomologous (restrictCocycle hPK g) f := hg
  exact cohomologous_trans (restrict_cohomologous hPK hFg) hgf

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Intermediate
variable {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]

private theorem closed_intermediate_image (P L : Subgroup J) (hL : IsClosed (L : Set J))
    (hPL : P ≤ L) (K : Subgroup L) (hK : IsClosed (K : Set L))
    (hPK : P.subgroupOf L ≤ K) (hproper : K < ⊤) :
    IsClosed (K.map L.subtype : Set J) ∧ P ≤ K.map L.subtype ∧ K.map L.subtype < L := by
  letI := profinite_closed_subgroup L hL
  refine ⟨(hK.isCompact.image continuous_subtype_val).isClosed, ?_, ?_⟩
  · simpa only [Subgroup.map_subgroupOf_eq_of_le hPL] using Subgroup.map_mono hPK (f := L.subtype)
  · refine lt_of_le_of_ne ((Subgroup.map_le_range L.subtype K).trans (le_of_eq L.range_subtype)) ?_
    intro he
    have he' : K.map L.subtype = (⊤ : Subgroup L).map L.subtype := by
      rw [← MonoidHom.range_eq_map, L.range_subtype, he]
    exact hproper.ne ((Subgroup.map_injective L.subtype_injective) he')

private theorem openNormal_lt_top_of_prime_index {L : Type*} [Group L] [TopologicalSpace L]
    (K : OpenNormalSubgroup L) (hq : K.toSubgroup.index.Prime) : K.toSubgroup < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  exact hq.ne_one (by rw [he, Subgroup.index_top])

end Intermediate

section Rebase
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



private theorem Cocycle.ExtendsTo.on_mapped_subgroup {P L : Subgroup J}
    {f : Cocycle (N := N) P} (K : Subgroup L) (hPK : P.subgroupOf L ≤ K)
    (h : f.ExtendsTo (K.map L.subtype)) :
    (f.onSubgroup (L := L)).ExtendsTo K := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPK, F.fromMappedSubgroup K, n, fun x => hn ⟨x, x.property⟩⟩

private theorem Cocycle.ExtendsTo.of_subgroup_top {P L : Subgroup J}
    {f : Cocycle (N := N) P} (hPL : P ≤ L)
    (h : (f.onSubgroup (L := L)).ExtendsTo ⊤) : f.ExtendsTo L := by
  obtain ⟨_, F, n, hn⟩ := h
  exact ⟨hPL, F.ofSubgroupTop, n, fun x => hn ⟨⟨x, hPL x.property⟩, x.property⟩⟩

end Rebase

section Restriction
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]







end Restriction
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The pronilpotent branch of Lemma 1.2, using the manuscript's two Zorn
arguments: first a fixed pair of cocycles, then one stable class. -/

namespace LocalConjugacy

private theorem pronilpotent_subgroup {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    (hJ : Pronilpotent J) (L : Subgroup J) : Pronilpotent L := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors L V
  letI := hJ U
  exact Group.nilpotent_of_surjective f hf



variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



/-- Surjectivity, by minimality for the single prescribed stable class.
Injectivity makes its lift invariant before Proposition 2.2 is applied. -/
private theorem pronilpotent_sylow_extension_zorn_preparedProof
    (hJ : Pronilpotent J) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (τ : Cocycle (N := N) P) (hτ : InvariantUnder ⊤ P τ) : τ.ExtendsTo ⊤ := by
  apply extendsTo_of_zorn_step P τ
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hJL := pronilpotent_subgroup hJ L
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  letI := sylowPro_normal_of_pronilpotent hJL (P.subgroupOf L) hPLs
  obtain ⟨J₀, hPJ₀, hprime, hne⟩ :=
    pronilpotent_prime_index_above_sylow hJL (P.subgroupOf L) hPLs hproper
  letI : Fact J₀.toSubgroup.index.Prime := ⟨hprime⟩
  have hτL : InvariantUnder ⊤ (P.subgroupOf L) (τ.onSubgroup (L := L)) := by
    intro j _
    obtain ⟨n, hn⟩ := hτ j trivial
    exact ⟨n, fun x hx hjx => hn x hx hjx⟩
  have hinj : ∀ φ ψ : Cocycle (J := L) (N := N) J₀.toSubgroup,
      Cohomologous (restrictCocycle hPJ₀ φ) (restrictCocycle hPJ₀ ψ) → Cohomologous φ ψ := by
    intro φ ψ hφψ
    letI := profinite_closed_subgroup J₀.toSubgroup J₀.isClosed
    have hJ₀ := pronilpotent_subgroup hJL J₀.toSubgroup
    have hPs := isSylowPro_subgroupOf J₀.toSubgroup (P.subgroupOf L) J₀.isClosed
      (isSylowPro_of_intermediate hPLs hPJ₀ le_top)
    have hh : Cohomologous φ.subgroupTop ψ.subgroupTop := by
      apply pronilpotent_sylow_restriction_injective_zorn hJ₀ hN _ hPs
      obtain ⟨n, hn⟩ := hφψ
      exact ⟨n, fun x => hn ⟨x, x.property⟩⟩
    obtain ⟨n, hn⟩ := hh
    exact ⟨n, fun x => hn ⟨x, trivial⟩⟩
  obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le
    J₀.toSubgroup J₀.isClosed hPJ₀ (openNormal_lt_top_of_prime_index J₀ hprime)
  have hext := (hmin _ hclosed hle hlt).on_mapped_subgroup J₀.toSubgroup hPJ₀
  exact Cocycle.ExtendsTo.of_subgroup_top hPL.le
    (extend_stable_class_across_prime_index (locallyFiniteGroup_of_finite N)
      hne hN J₀.toSubgroup (P.subgroupOf L) hPJ₀ J₀.isClosed rfl hinj
      (τ.onSubgroup (L := L)) hτL hext)

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hJ : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1} J inst inst_2) {p : Nat} [Fact (Nat.Prime p)]
  (hN : @IsPGroup.{u_2} p N inst_1) (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (τ : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P)
  (hτ :
    @LocalConjugacy.Proof.LocalConjugacy.InvariantUnder.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P τ),
  @LocalConjugacy.Proof.LocalConjugacy.Cocycle.ExtendsTo.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P τ
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
  @LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_extension_zorn_preparedProof
