-- Prove2me | solution 1 for GlobalTheory.character_mem_lattice_of_comul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:50:35.705103+00:00
-- url     : https://prove2.me/submissions/10db0167-f769-4844-aa6e-f6f1a7b44d80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CharacterMemLatticeOfComul
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem latConv_sum {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C)
    {m : ℕ} (f : N → C) (g h : Fin m → N → C) (hf : ∀ x y, f (x + y) = ∑ i, g i x * h i y) :
    latConv φ ψ f = ∑ i, φ (g i) * ψ (h i) := by
  have h1 : ∀ x, (fun y => f (x + y)) = ∑ i, g i x • h i := by
    intro x; funext y; simp [hf, Finset.sum_apply]
  have h2 : (fun x => ψ (fun y => f (x + y))) = ∑ i, ψ (h i) • g i := by
    funext x; rw [h1]; simp [Finset.sum_apply, mul_comm]
  change φ (fun x => ψ (fun y => f (x + y))) = _
  rw [h2]; simp [mul_comm]
private theorem lat_bound {C V : Type} [Field C] [AddCommGroup V] [Module C V]
    (v : Valuation C NNReal) (S : Set V) {k : V} (hk : k ∈ Submodule.span C S) :
    ∃ M : NNReal, ∀ φ : V →ₗ[C] C, (∀ f ∈ S, v (φ f) ≤ 1) → v (φ k) ≤ M := by
  induction hk using Submodule.span_induction with
  | mem x hx => exact ⟨1, fun φ hφ => hφ x hx⟩
  | zero => exact ⟨0, fun φ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨max M M', fun φ hφ => ?_⟩
    rw [map_add]
    exact (v.map_add _ _).trans (max_le_max (hM φ hφ) (hM' φ hφ))
  | smul c x _ hx =>
    obtain ⟨M, hM⟩ := hx
    refine ⟨v c * M, fun φ hφ => ?_⟩
    rw [map_smul, smul_eq_mul, map_mul]
    gcongr
    exact hM φ hφ
private theorem lat_dual {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {N : Type} (A : Submodule O (N → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (N → C)) = ⊤) (k : N → C)
    (hk : ∀ φ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (φ f) ≤ 1) → v (φ k) ≤ 1) : k ∈ A := by
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : N → C) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → N → C := fun i => (b i : N → C)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hb : ∀ i, bC i = w i := fun i => Module.Basis.mk_apply _ _ _
  have hco : ∀ i, ∀ f ∈ A, v (bC.coord i f) ≤ 1 := by
    intro i f hf
    rw [← hspR] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [← algebraMap_smul C c x, map_smul, smul_eq_mul, map_mul]
      exact mul_le_one' (hv.map_le_one c) hx
  rw [← bC.sum_repr k]
  refine A.sum_mem fun i _ => ?_
  obtain ⟨o, ho⟩ := hv.exists_of_le_one (hk _ (hco i))
  have ho' : bC.repr k i = algebraMap O C o := ho.symm
  rw [ho', algebraMap_smul, hb]
  exact A.smul_mem _ (b i).2
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (N : Type) [AddCommMonoid N] [Finite N] (A : Submodule O (N → C)), A.FG → Submodule.span C (A : Set (N → C)) = ⊤ → (∀ f ∈ A, ∃ (m : ℕ) (g h : Fin m → N → C), (∀ i, g i ∈ A) ∧ (∀ i, h i ∈ A) ∧ ∀ x y, f (x + y) = ∑ i, g i x * h i y) → (∀ f ∈ A, ∃ o : O, algebraMap O C o = f 0) → ∀ κ : N → C, κ 0 = 1 → (∀ x y, κ (x + y) = κ x * κ y) → κ ∈ A := by
  intro C _ v O _ _ hv N _ _ A hfg hsp hco h0 k hk0 hk
  refine lat_dual v hv A hfg hsp k fun φ hφ => ?_
  obtain ⟨M, hM⟩ := lat_bound v (A : Set (N → C)) (k := k) (by rw [hsp]; trivial)
  have hpow : ∀ n : ℕ, ∃ ψ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (ψ f) ≤ 1) ∧ ψ k = φ k ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨LinearMap.proj 0, fun f hf => ?_, by simpa using hk0⟩
      obtain ⟨o, ho⟩ := h0 f hf
      rw [LinearMap.proj_apply, ← ho]
      exact hv.map_le_one o
    | succ n ih =>
      obtain ⟨ψ, hψ, hψk⟩ := ih
      refine ⟨latConv ψ φ, fun f hf => ?_, ?_⟩
      · obtain ⟨m, g, h, hg, hh, hf⟩ := hco f hf
        rw [latConv_sum ψ φ f g h hf]
        refine v.map_sum_le fun i _ => ?_
        rw [map_mul]
        exact mul_le_one' (hψ _ (hg i)) (hφ _ (hh i))
      · rw [latConv_sum ψ φ k (fun _ : Fin 1 => k) (fun _ => k) (by simpa using hk)]
        simp [hψk, pow_succ]
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  obtain ⟨ψ, hψ, hψk⟩ := hpow n
  have := hM ψ hψ
  rw [hψk, map_pow] at this
  exact absurd hn (not_lt.2 this)
end GlobalTheory
