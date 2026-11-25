-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFiniteLength_of_coinvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:44.408811+00:00
-- url     : https://prove2.me/submissions/f278b40d-96aa-4016-ad0a-f0db7019bfce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_map_mem_coinvariantsKer
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_subrep
import Theorems.Thm_GroundTheory_Automorphic_mem_ker_subrep_of_mem_ker
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedGT
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedLT
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_irreducible_quotient
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_quotient
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotientMk_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotientMk_surjective
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_strictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution {V : Type u} [AddCommGroup V] [Module ℂ V]
    {X : Representation ℂ G V} (hX : IsSmooth X) {ι : Type*} [Finite ι] (N : ι → Subgroup G)
    [∀ i, LocallyCompactSpace (N i)] [∀ i, T2Space (N i)] [∀ i, TotallyDisconnectedSpace (N i)]
    (hN : ∀ i (s : Finset (N i)), ∃ K : Subgroup (N i), IsCompact (K : Set (N i)) ∧
      IsOpen (K : Set (N i)) ∧ ∀ x ∈ s, x ∈ K)
    {M : ι → Type*} [∀ i, Group (M i)]
    (τ : ∀ i, Representation ℂ (M i) (Representation.Coinvariants (X.comp (N i).subtype)))
    (hτ : ∀ i m, ∃ g : G, ∃ c : ℂ, ∀ v, τ i m (Representation.Coinvariants.mk _ v) =
      c • Representation.Coinvariants.mk _ (X g v))
    (hfin : ∀ i, HasFiniteLength (τ i))
    (hfaith : ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
      [π.IsIrreducible], IsSmooth π → IsSubquotient π X →
        ∃ i, Nontrivial (Representation.Coinvariants (π.comp (N i).subtype))) :
    HasFiniteLength X := by
  classical
  have := fun i => (hfin i).wellFoundedLT
  have := fun i => (hfin i).wellFoundedGT
  let Λ : Subrepresentation X → ∀ i, Subrepresentation (τ i) := fun A i =>
    ⟨A.toSubmodule.map (Representation.Coinvariants.mk (X.comp (N i).subtype)), by
      rintro m _ ⟨v, hv, rfl⟩
      obtain ⟨g, c, hgc⟩ := hτ i m
      rw [hgc]
      exact Submodule.smul_mem _ c ⟨X g v, A.apply_mem_toSubmodule g hv, rfl⟩⟩
  have hmono : ∀ A B : Subrepresentation X, A ≤ B → ∀ i, Λ A i ≤ Λ B i :=
    fun A B h i _ ⟨v, hv, hvy⟩ => ⟨v, h hv, hvy⟩
  refine hasFiniteLength_of_strictMono Λ fun A B hAB => ?_
  rw [Pi.lt_def]
  refine ⟨hmono A B hAB.le, ?_⟩
  by_contra hne'
  have hne : ∀ i, ¬ Λ A i < Λ B i := fun i h => hne' ⟨i, h⟩
  have heq : ∀ i, Λ A i = Λ B i := fun i =>
    (lt_or_eq_of_le (hmono A B hAB.le i)).resolve_left (hne i)

  obtain ⟨x, hxB, hxA⟩ := SetLike.exists_of_lt hAB
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => X g x)
  have hS : ∀ g, S ≤ S.comap (X g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let Cs : Submodule ℂ V := A.toSubmodule ⊔ S
  have hCs : ∀ g, Cs ≤ Cs.comap (X g) := fun g => sup_le
    (fun v hv => Submodule.mem_sup_left (A.apply_mem_toSubmodule g hv))
    (fun v hv => Submodule.mem_sup_right (hS g hv))
  let C : Subrepresentation X := ⟨Cs, fun g v hv => hCs g hv⟩
  have hxC : x ∈ Cs := Submodule.mem_sup_right (Submodule.subset_span ⟨1, by simp⟩)
  have hCB : ∀ v ∈ Cs, v ∈ B := fun v hv => (sup_le (show A.toSubmodule ≤ B.toSubmodule from hAB.le)
    (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact B.apply_mem_toSubmodule g hxB))) hv
  let Y0 : Submodule ℂ Cs := A.toSubmodule.comap Cs.subtype
  have hY0 : ∀ g, Y0 ≤ Y0.comap (C.toRepresentation g) := fun g v hv =>
    A.apply_mem_toSubmodule g hv
  let Q := Representation.quotient C.toRepresentation Y0 hY0
  let q₀ : Cs ⧸ Y0 := Submodule.Quotient.mk ⟨x, hxC⟩
  have hq₀ : q₀ ≠ 0 := fun h => hxA ((Submodule.Quotient.mk_eq_zero Y0 (x := (⟨x, hxC⟩ : Cs))).1 h)
  have : Nontrivial (Cs ⧸ Y0) := ⟨⟨q₀, 0, hq₀⟩⟩
  have hgen : Submodule.span ℂ {y | ∃ g, ∃ s ∈ ({q₀} : Finset (Cs ⧸ Y0)), y = Q g s} = ⊤ := by
    set T := Submodule.span ℂ {y | ∃ g, ∃ s ∈ ({q₀} : Finset (Cs ⧸ Y0)), y = Q g s}
    have hle : Cs ≤ (T.comap Y0.mkQ).map Cs.subtype := by
      refine sup_le (fun a ha => ⟨⟨a, Submodule.mem_sup_left ha⟩, ?_, rfl⟩)
        (Submodule.span_le.2 ?_)
      · show Submodule.Quotient.mk _ ∈ T
        rw [(Submodule.Quotient.mk_eq_zero Y0 (x := (⟨a, Submodule.mem_sup_left ha⟩ : Cs))).2 ha]
        exact T.zero_mem
      · rintro _ ⟨g, rfl⟩
        refine ⟨⟨X g x, hCs g hxC⟩, Submodule.subset_span ⟨g, q₀, Finset.mem_singleton_self _, rfl⟩,
          rfl⟩
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective Y0 y
    obtain ⟨c', hc', hcc'⟩ := hle c.2
    rw [show c = c' from Subtype.ext hcc'.symm]
    exact hc'
  obtain ⟨Z, hZ, hirr⟩ := exists_irreducible_quotient (τ := Q) {q₀} hgen
  let π := Representation.quotient Q Z hZ
  let p : Representation.IntertwiningMap C.toRepresentation π :=
    (quotientMk Z hZ).comp (quotientMk Y0 hY0)
  have hp : Surjective p := (quotientMk_surjective Z hZ).comp (quotientMk_surjective Y0 hY0)
  have hπs : IsSmooth π := isSmooth_quotient (isSmooth_quotient (isSmooth_subrep hX C) Y0 hY0) Z hZ
  obtain ⟨i, hi⟩ := hfaith _ π hπs ⟨C, p, hp⟩

  have key : ∀ c : Cs, p c ∈ Representation.Coinvariants.ker (π.comp (N i).subtype) := by
    intro c
    have hmem : Representation.Coinvariants.mk (X.comp (N i).subtype) (c : V) ∈
        (Λ B i).toSubmodule := ⟨c, hCB c c.2, rfl⟩
    rw [← heq i] at hmem
    obtain ⟨a, ha, hac⟩ := hmem
    have haC : a ∈ Cs := Submodule.mem_sup_left ha
    have hk : ((c - ⟨a, haC⟩ : Cs) : V) ∈
        Representation.Coinvariants.ker (X.comp (N i).subtype) := by
      rw [← Representation.Coinvariants.mk_eq_zero]
      simp only [Submodule.coe_sub, map_sub]
      rw [← hac, sub_self]
    have hk' := mem_ker_subrep_of_mem_ker (N i) (hN i) hX C hk
    have hpa : p ⟨a, haC⟩ = 0 := by
      show quotientMk Z hZ (quotientMk Y0 hY0 ⟨a, haC⟩) = 0
      rw [quotientMk_apply Y0, (Submodule.Quotient.mk_eq_zero _).2 (show (⟨a, haC⟩ : Cs) ∈ Y0 from ha),
        map_zero]
    have := map_mem_coinvariantsKer p (N i) hk'
    rwa [map_sub, hpa, sub_zero] at this
  refine (not_subsingleton_iff_nontrivial.2 hi) ⟨fun y z => ?_⟩
  have hall : ∀ y : Representation.Coinvariants (π.comp (N i).subtype), y = 0 := by
    intro y
    obtain ⟨q, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    obtain ⟨c, rfl⟩ := hp q
    exact (Representation.Coinvariants.mk_eq_zero _).2 (key c)
  rw [hall y, hall z]
end GroundTheory.Automorphic
