-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_trivial_on_intersection
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:58:25.419266+00:00
-- url     : https://prove2.me/submissions/1c1d7d53-3185-4bb5-a83e-1401ec657cad

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_procyclic_commutative

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



/-- A continuous homomorphism into a discrete group sends pro-`p` elements
to elements of finite `p`-power order. No finiteness of the codomain is needed. -/
private theorem image_pow {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]
    {p : ℕ} (h : IsProP p G) (f : G →* F) (hf : Continuous f) (x : G) :
    ∃ k : ℕ, f x ^ p ^ k = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  obtain ⟨k, hk⟩ := h U (QuotientGroup.mk' U.toSubgroup x)
  refine ⟨k, ?_⟩
  have he := congrArg (QuotientGroup.lift U.toSubgroup f (by rfl)) hk
  simpa using he

/-- The continuity argument needed at the end of Proposition 2.1, valid
even for an infinite discrete coefficient `p`-group. -/
private theorem continuous_hom_eq_one_of_coprime {G N : Type*} [Group G] [Group N]
    [TopologicalSpace G] [TopologicalSpace N] [DiscreteTopology N]
    {p q : ℕ} (hG : IsProP q G) (hN : IsPGroup p N) (hpq : p.Coprime q)
    (f : G →* N) (hf : Continuous f) (x : G) : f x = 1 := by
  obtain ⟨a, ha⟩ := hN (f x)
  obtain ⟨b, hb⟩ := image_pow hG f hf x
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hpq.pow a b)
    (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb)







end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]







private theorem isPGroup_quotient_image {p : ℕ} (H : Subgroup G) (hH : IsProP p H)
    (U : OpenNormalSubgroup G) : IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  let π := QuotientGroup.mk' U.toSubgroup
  let f : H →* G ⧸ U.toSubgroup := π.comp H.subtype
  have hf : Continuous f := continuous_quotient_mk'.comp continuous_subtype_val
  intro x
  obtain ⟨y, hy, he⟩ := x.property
  obtain ⟨k, hk⟩ := image_pow hH f hf ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  change x.val ^ p ^ k = 1
  change π y ^ p ^ k = 1 at hk
  rwa [show π y = x.val from he] at hk

private theorem isProP_mono {p : ℕ} {P H : Subgroup G} (hPH : P ≤ H)
    (hH : IsProP p H) : IsProP p P := by
  apply isProP_of_quotient_images
  intro U
  exact (isPGroup_quotient_image H hH U).to_le (Subgroup.map_mono hPH)

namespace FiniteSylowSystem
open CategoryTheory















variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)







include hP







end FiniteSylowSystem





























end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped IsMulCommutative



section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [DiscreteTopology N] [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The second conclusion of Proposition 2.1 follows from continuity and
coprime orders, for possibly infinite discrete coefficient groups. -/
private theorem fixed_cocycle_trivial_on_intersection_preparedProof
    {p q : ℕ} (hpq : p.Coprime q) (hN : IsPGroup p N)
    (K Q : Subgroup J) [K.Normal] (hcyclic : Procyclic Q) (hQ : IsProP q Q)
    (g : Cocycle (N := N) K) (hfix : ∀ x : Q, twistCocycle g x = g) :
    ∀ x ∈ Q, ∀ hx : x ∈ K, g.toFun ⟨x, hx⟩ = 1 := by
  let R := Q ⊓ K
  have ha (x y : R) : (x : J) • g.toFun ⟨y, y.property.2⟩ =
      g.toFun ⟨y, y.property.2⟩ := by
    have he := congrArg (fun f : Cocycle (N := N) K => f.toFun ⟨y, y.property.2⟩)
      (hfix ⟨x, x.property.1⟩)
    change (x : J) • g.toFun ⟨(x : J)⁻¹ * y * x, _⟩ = g.toFun ⟨y, y.property.2⟩ at he
    have hxy := congrArg Subtype.val
      (procyclic_commutative hcyclic (⟨x, x.property.1⟩ : Q) ⟨y, y.property.1⟩)
    change (x : J) * y = (y : J) * x at hxy
    have hc : (x : J)⁻¹ * y * x = y := by rw [mul_assoc, ← hxy]; group
    simpa only [hc] using he
  let φ : R →* N :=
    { toFun := fun x => g.toFun ⟨x, x.property.2⟩
      map_one' := cocycle_one g
      map_mul' := fun x y => by
        change g.toFun ((⟨x, x.property.2⟩ : K) * ⟨y, y.property.2⟩) = _
        rw [g.map_mul, ha x y] }
  have hφ : Continuous φ := g.continuous_toFun.comp
    (continuous_subtype_val.subtype_mk (fun x : R => x.property.2))
  have hR : IsProP q R := isProP_mono inf_le_left hQ
  intro x hx hxK
  exact continuous_hom_eq_one_of_coprime hR hN hpq φ hφ ⟨x, hx, hxK⟩



end

section
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]



end
end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1] [@DiscreteTopology.{u_2} N inst_4]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_8 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  {p q : Nat} (hpq : Nat.Coprime p q) (hN : @IsPGroup.{u_2} p N inst_1) (K Q : @Subgroup.{u_1} J inst)
  [inst_9 : @Subgroup.Normal.{u_1} J inst K]
  (hcyclic :
    @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (g : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
  (hfix :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
      @Eq.{max (u_1 + 1) (u_2 + 1)}
        (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
        (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4 inst_7
          inst_8 K inst_9 g
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                x)
            x))
        g)
  (x : J),
  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x →
    ∀
      (hx :
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
      @Eq.{u_2 + 1} N
        (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K g
          (@Subtype.mk.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                x)
            x hx))
        (@OfNat.ofNat.{u_2} N (nat_lit 1)
          (@One.toOfNat1.{u_2} N
            (@InvOneClass.toOne.{u_2} N
              (@DivInvOneMonoid.toInvOneClass.{u_2} N
                (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1)))))) :=
  @LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_trivial_on_intersection_preparedProof
