-- Prove2me | solution 1 for GlobalTheory.exists_reps_ideal_inv_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:43.926372+00:00
-- url     : https://prove2.me/submissions/97529663-a2c0-4330-8318-a8a27b103f9a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MinorSmulEqRowSpaceOfCofVecOrth
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_projQuotCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (S0 : Submodule (𝓞 K) V) (J : Ideal (𝓞 K)) (hS : S0.FG)
    (hJ : J ≠ ⊥) :
    ∃ R : Finset V, R.card ≤ Ideal.absNorm J ^ finrank K (Submodule.span K (S0 : Set V)) ∧
      ∀ x : V, (∀ j ∈ J, j • x ∈ S0) → ∃ y ∈ R, x - y ∈ S0 := by
  classical
  let P : Submodule (𝓞 K) V :=
    { carrier := {x | ∀ j ∈ J, j • x ∈ S0}
      add_mem' := fun {a b} ha hb j hj => by
        rw [smul_add]; exact S0.add_mem (ha j hj) (hb j hj)
      zero_mem' := fun j hj => by simp
      smul_mem' := fun c x hx j hj => by
        rw [smul_comm]; exact S0.smul_mem c (hx j hj) }
  obtain ⟨j₀, hj₀, hj₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hj₀K : algebraMap (𝓞 K) K j₀ ≠ 0 := fun h => hj₀0 (hinj (by simpa using h))
  have : Module.IsTorsionFree (𝓞 K) V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    rw [← algebraMap_smul K c x, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h
  have : Module.Finite (𝓞 K) S0 := Module.Finite.iff_fg.mpr hS
  let f : P →ₗ[𝓞 K] S0 := (j₀ • P.subtype).codRestrict S0 (fun x => x.2 j₀ hj₀)
  have hf : Function.Injective f := by
    intro x y h
    have h' : j₀ • (x : V) = j₀ • (y : V) := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective V hj₀0 h')
  have : Module.Finite (𝓞 K) P := Module.Finite.of_injective f hf
  have : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 K) P := inferInstance
  have : Module.Projective (𝓞 K) P := Module.Flat.projective_of_finitePresentation
  have hcard := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K P J hJ
  have hN : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hrk : finrank (𝓞 K) P ≤ finrank K (Submodule.span K (S0 : Set V)) := by
    obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := P) le_rfl
    have hmem : ∀ i, (g i : V) ∈ Submodule.span K (S0 : Set V) := by
      intro i
      have h1 : j₀ • (g i : V) ∈ Submodule.span K (S0 : Set V) :=
        Submodule.subset_span ((g i).2 j₀ hj₀)
      rw [← algebraMap_smul K j₀] at h1
      exact (Submodule.smul_mem_iff _ hj₀K).mp h1
    have hg1 : LinearIndependent (𝓞 K) (fun i => (g i : V)) :=
      hg.map' P.subtype (Submodule.ker_subtype P)
    have hg2 : LinearIndependent K (fun i => (g i : V)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hg1
    have hg3 : LinearIndependent K
        (fun i => (⟨g i, hmem i⟩ : Submodule.span K (S0 : Set V))) :=
      LinearIndependent.of_comp (Submodule.span K (S0 : Set V)).subtype hg2
    simpa using hg3.fintype_card_le_finrank
  have : Finite (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hN)
  have : Fintype (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) => ((Quotient.out q : P) : V)),
    ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) hrk
  · intro x hx
    let x' : P := ⟨x, hx⟩
    let q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) := Submodule.Quotient.mk x'
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h1 : x' - Quotient.out q ∈ (J • ⊤ : Submodule (𝓞 K) P) :=
      (Submodule.Quotient.eq _).mp (Quotient.out_eq q).symm
    have h2 : ∀ z ∈ (J • ⊤ : Submodule (𝓞 K) P), (z : V) ∈ S0 := by
      intro z hz
      refine Submodule.smul_induction_on hz (fun j hj n _ => n.2 j hj) (fun a b ha hb => ?_)
      exact S0.add_mem ha hb
    exact h2 _ h1
end GlobalTheory
