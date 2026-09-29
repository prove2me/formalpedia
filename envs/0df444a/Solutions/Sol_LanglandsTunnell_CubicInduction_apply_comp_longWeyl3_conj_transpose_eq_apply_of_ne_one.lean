-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9de6c8fa-364a-5ad8-8ff9-bd539558a2e5

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Image
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one

set_option autoImplicit false

section

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatSpace

section Space

variable (X : Type*) [TopologicalSpace X]

private abbrev testSpace : Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X}

private theorem mem_testSpace {f : X → ℂ} : f ∈ testSpace X ↔ IsSchwartzBruhat f :=
  Iff.rfl

private theorem mem_testSpace_iff {f : X → ℂ} : f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

private theorem isLocallyConstant_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsLocallyConstant f :=
  hf.1

private theorem hasCompactSupport_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : HasCompactSupport f :=
  hf.2

private theorem mem_testSpace_of {f : X → ℂ} (h₁ : IsLocallyConstant f) (h₂ : HasCompactSupport f) :
    f ∈ testSpace X :=
  ⟨h₁, h₂⟩

private theorem indicator_mem_testSpace {U : Set X} (hU : IsClopen U) (hUc : IsCompact U) (c : ℂ) :
    (U.indicator fun _ => c) ∈ testSpace X :=
  IsSchwartzBruhat.indicator_const hU hUc c

private theorem mul_mem_testSpace {e f : X → ℂ} (he : IsLocallyConstant e) (hf : f ∈ testSpace X) :
    e * f ∈ testSpace X :=
  ⟨he.mul hf.1, hf.2.mul_left⟩

private theorem isClopen_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsClopen (Function.support f) := by
  have h : Function.support f = {x | f x = 0}ᶜ := by
    ext x
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq]
  rw [h]
  exact (hf.1.isClopen_fiber 0).compl

private theorem isCompact_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsCompact (Function.support f) :=
  (hasCompactSupport_of_mem hf).isCompact.of_isClosed_subset (isClopen_support_of_mem hf).isClosed (subset_tsupport _)

end Space

section Extend

variable {X : Type*} {U : Set X}

private def extendFun (f : U → ℂ) : X → ℂ :=
  Function.extend Subtype.val f 0

private theorem extendFun_apply_coe (f : U → ℂ) (u : U) : extendFun f (u : X) = f u :=
  Subtype.val_injective.extend_apply f 0 u

private theorem extendFun_apply_of_mem (f : U → ℂ) {x : X} (hx : x ∈ U) : extendFun f x = f ⟨x, hx⟩ :=
  extendFun_apply_coe f ⟨x, hx⟩

private theorem extendFun_apply_of_notMem (f : U → ℂ) {x : X} (hx : x ∉ U) : extendFun f x = 0 := by
  unfold extendFun
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, rfl⟩
    exact hx u.2

private theorem extendFun_add (f g : U → ℂ) : extendFun (f + g) = extendFun f + extendFun g := by
  funext x
  by_cases hx : x ∈ U
  · rw [Pi.add_apply, extendFun_apply_of_mem _ hx, extendFun_apply_of_mem _ hx, extendFun_apply_of_mem _ hx,
      Pi.add_apply]
  · simp only [Pi.add_apply, extendFun_apply_of_notMem _ hx, add_zero]

private theorem extendFun_smul (c : ℂ) (f : U → ℂ) : extendFun (c • f) = c • extendFun f := by
  funext x
  by_cases hx : x ∈ U
  · rw [Pi.smul_apply, extendFun_apply_of_mem _ hx, extendFun_apply_of_mem _ hx, Pi.smul_apply]
  · simp only [Pi.smul_apply, extendFun_apply_of_notMem _ hx, smul_zero]

private theorem support_extendFun (f : U → ℂ) :
    Function.support (extendFun f) = Subtype.val '' Function.support f := by
  ext x
  constructor
  · intro hx
    by_cases hxU : x ∈ U
    · rw [Function.mem_support, extendFun_apply_of_mem f hxU] at hx
      exact ⟨⟨x, hxU⟩, hx, rfl⟩
    · exact absurd (extendFun_apply_of_notMem f hxU) (Function.mem_support.mp hx)
  · rintro ⟨u, hu, rfl⟩
    rw [Function.mem_support, extendFun_apply_coe]
    exact Function.mem_support.mp hu

variable [TopologicalSpace X] [T2Space X]

private theorem isLocallyConstant_extendFun (hU : IsOpen U) {f : U → ℂ} (hf : f ∈ testSpace U) :
    IsLocallyConstant (extendFun f) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  by_cases hy : y = 0
  · subst hy
    have h : extendFun f ⁻¹' {0} = (Subtype.val '' Function.support f)ᶜ := by
      rw [← support_extendFun]
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Function.mem_support, ne_eq, not_not]
    rw [h]
    exact (((isCompact_support_of_mem hf).image continuous_subtype_val).isClosed).isOpen_compl
  · have h : extendFun f ⁻¹' {y} = Subtype.val '' (f ⁻¹' {y}) := by
      ext x
      constructor
      · intro hx
        by_cases hxU : x ∈ U
        · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rwa [extendFun_apply_of_mem f hxU] at hx
        · exfalso
          simp only [Set.mem_preimage, Set.mem_singleton_iff, extendFun_apply_of_notMem f hxU] at hx
          exact hy hx.symm
      · rintro ⟨u, hu, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu ⊢
        rwa [extendFun_apply_coe]
    rw [h]
    exact hU.isOpenMap_subtype_val _ (isLocallyConstant_of_mem hf {y})

private theorem extendFun_mem (hU : IsOpen U) {f : U → ℂ} (hf : f ∈ testSpace U) : extendFun f ∈ testSpace X :=
  ⟨isLocallyConstant_extendFun hU hf, (hasCompactSupport_of_mem hf).extend_zero continuous_subtype_val⟩

private def extendByZero (hU : IsOpen U) : testSpace U →ₗ[ℂ] testSpace X where
  toFun f := ⟨extendFun (f : U → ℂ), extendFun_mem hU f.2⟩
  map_add' f g := Subtype.ext (extendFun_add (f : U → ℂ) g)
  map_smul' c f := Subtype.ext (extendFun_smul c (f : U → ℂ))

private theorem coe_extendByZero (hU : IsOpen U) (f : testSpace U) :
    (extendByZero hU f : X → ℂ) = extendFun (f : U → ℂ) :=
  rfl

private theorem extendByZero_apply_coe (hU : IsOpen U) (f : testSpace U) (u : U) :
    (extendByZero hU f : X → ℂ) (u : X) = (f : U → ℂ) u :=
  extendFun_apply_coe _ u

private theorem extendByZero_apply_of_notMem (hU : IsOpen U) (f : testSpace U) {x : X} (hx : x ∉ U) :
    (extendByZero hU f : X → ℂ) x = 0 :=
  extendFun_apply_of_notMem _ hx

private theorem extendByZero_injective (hU : IsOpen U) : Function.Injective (extendByZero hU) := by
  intro f g hfg
  apply Subtype.ext
  funext u
  have h := congrArg (fun φ : testSpace X => (φ : X → ℂ) (u : X)) hfg
  simpa only [extendByZero_apply_coe] using h

private theorem mem_range_extendByZero_iff (hU : IsOpen U) {g : testSpace X} :
    g ∈ LinearMap.range (extendByZero hU) ↔ ∀ x, x ∉ U → (g : X → ℂ) x = 0 := by
  constructor
  · rintro ⟨f, rfl⟩ x hx
    exact extendByZero_apply_of_notMem hU f hx
  · intro hg
    have hsupp : Function.support (g : X → ℂ) ⊆ U := fun x hx => by
      by_contra hxU
      exact Function.mem_support.mp hx (hg x hxU)
    set f : U → ℂ := fun u => (g : X → ℂ) u with hf_def
    have hf₁ : IsLocallyConstant f := (isLocallyConstant_of_mem g.2).comp_continuous continuous_subtype_val
    have hfsupp : Function.support f = Subtype.val ⁻¹' Function.support (g : X → ℂ) := by
      ext u
      simp only [Function.mem_support, Set.mem_preimage, hf_def]
    have hK : IsCompact (Function.support f) := by
      rw [hfsupp]
      refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).mpr (isCompact_support_of_mem g.2)
      rw [Subtype.range_val]
      exact hsupp
    have hKc : IsClosed (Function.support f) := by
      rw [hfsupp]
      exact (isClopen_support_of_mem g.2).isClosed.preimage continuous_subtype_val
    have hf₂ : HasCompactSupport f :=
      HasCompactSupport.intro' hK hKc fun u hu => by simpa using hu
    refine ⟨⟨f, hf₁, hf₂⟩, ?_⟩
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U
    · exact extendByZero_apply_coe hU ⟨f, hf₁, hf₂⟩ ⟨x, hx⟩
    · rw [extendByZero_apply_of_notMem hU _ hx, hg x hx]

end Extend

section Restrict

variable {X : Type*} [TopologicalSpace X] {Z : Set X}

private theorem restrictFun_mem (hZ : IsClosed Z) {f : X → ℂ} (hf : f ∈ testSpace X) :
    (f ∘ Subtype.val : Z → ℂ) ∈ testSpace Z :=
  ⟨(isLocallyConstant_of_mem hf).comp_continuous continuous_subtype_val,
    (hasCompactSupport_of_mem hf).comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩

private def restrictClosed (hZ : IsClosed Z) : testSpace X →ₗ[ℂ] testSpace Z where
  toFun f := ⟨(f : X → ℂ) ∘ Subtype.val, restrictFun_mem hZ f.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem restrictClosed_apply (hZ : IsClosed Z) (f : testSpace X) (z : Z) :
    (restrictClosed hZ f : Z → ℂ) z = (f : X → ℂ) z :=
  rfl

private theorem restrictClosed_eq_zero_iff (hZ : IsClosed Z) {f : testSpace X} :
    restrictClosed hZ f = 0 ↔ ∀ x ∈ Z, (f : X → ℂ) x = 0 := by
  constructor
  · intro h x hx
    have := congrArg (fun φ : testSpace Z => (φ : Z → ℂ) ⟨x, hx⟩) h
    simpa [restrictClosed_apply] using this
  · intro h
    apply Subtype.ext
    funext z
    exact h z z.2

private theorem ker_restrictClosed [T2Space X] (hZ : IsClosed Z) :
    LinearMap.ker (restrictClosed hZ) = LinearMap.range (extendByZero hZ.isOpen_compl) := by
  ext g
  rw [LinearMap.mem_ker, restrictClosed_eq_zero_iff, mem_range_extendByZero_iff]
  constructor
  · intro h x hx
    exact h x (Set.notMem_compl_iff.mp hx)
  · intro h x hx
    exact h x (Set.notMem_compl_iff.mpr hx)

end Restrict

section Surjective

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

private theorem exists_isCompact_isClopen_between {K O : Set X} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ O := by
  have hpt : ∀ x ∈ K, ∃ W : Set X, IsCompact W ∧ IsClopen W ∧ x ∈ W ∧ W ⊆ O := by
    intro x hx
    obtain ⟨C, hC, hxC, hCO⟩ := exists_compact_subset hO (hKO hx)
    obtain ⟨W, (hW : IsClopen W), hxW, hWC⟩ :=
      TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open loc_compact_Haus_tot_disc_of_zero_dim hxC
        isOpen_interior
    exact ⟨W, hC.of_isClosed_subset hW.isClosed (hWC.trans interior_subset), hW, hxW,
      (hWC.trans interior_subset).trans hCO⟩
  choose! W hWc hWclopen hxW hWO using hpt
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover W fun x hx => (hWclopen x hx).isOpen.mem_nhds (hxW x hx)
  refine ⟨⋃ x ∈ t, W x, t.isCompact_biUnion fun x hx => hWc x (htK x hx),
    isClopen_biUnion_finset fun x hx => hWclopen x (htK x hx), hKt, ?_⟩
  intro y hy
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨x, hx, hyx⟩ := hy
  exact hWO x (htK x hx) hyx

private theorem restrictClosed_surjective {Z : Set X} (hZ : IsClosed Z) : Function.Surjective (restrictClosed hZ) := by
  intro h
  classical

  set S : Set Z := Function.support (h : Z → ℂ) with hS_def
  have hScomp : IsCompact S := isCompact_support_of_mem h.2
  have hfin : ((h : Z → ℂ) '' S).Finite := by
    haveI : CompactSpace S := isCompact_iff_compactSpace.mp hScomp
    have hlc : IsLocallyConstant ((h : Z → ℂ) ∘ (Subtype.val : S → Z)) :=
      h.2.1.comp_continuous continuous_subtype_val
    have := hlc.range_finite
    rwa [Set.range_comp, Subtype.range_val] at this

  have hbetween : ∀ c : ℂ, ∃ V : Set X, IsCompact V ∧ IsClopen V ∧
      Subtype.val '' (S ∩ {z | (h : Z → ℂ) z = c}) ⊆ V ∧ V ⊆ (Subtype.val '' {z | (h : Z → ℂ) z = c}ᶜ)ᶜ := by
    intro c
    have hfib : IsClopen {z | (h : Z → ℂ) z = c} := (isLocallyConstant_of_mem h.2).isClopen_fiber c
    refine exists_isCompact_isClopen_between ?_ ?_ ?_
    · exact (hScomp.of_isClosed_subset ((isClopen_support_of_mem h.2).isClosed.inter hfib.isClosed)
        Set.inter_subset_left).image continuous_subtype_val
    · exact (hZ.isClosedEmbedding_subtypeVal.isClosedMap _ hfib.isOpen.isClosed_compl).isOpen_compl
    · rintro x ⟨z, ⟨_, hzc⟩, rfl⟩
      rw [Set.mem_compl_iff]
      rintro ⟨z', hz', hzz'⟩
      cases Subtype.val_injective hzz'
      exact hz' hzc
  choose V hVc hVclopen hSV hVZ using hbetween
  refine ⟨∑ c ∈ hfin.toFinset,
    (⟨(V c).indicator fun _ => c, indicator_mem_testSpace (hVclopen c) (hVc c) c⟩ : testSpace X), ?_⟩
  apply Subtype.ext
  funext z
  rw [restrictClosed_apply, Submodule.coe_sum, Finset.sum_apply]
  dsimp only

  have hforce : ∀ c : ℂ, (z : X) ∈ V c → (h : Z → ℂ) z = c := by
    intro c hzc
    by_contra hne
    have hc := hVZ c hzc
    rw [Set.mem_compl_iff] at hc
    exact hc ⟨z, hne, rfl⟩
  rw [Finset.sum_eq_single ((h : Z → ℂ) z)]
  · by_cases hz0 : (h : Z → ℂ) z = 0
    · simp only [hz0, Set.indicator_apply, ite_self]
    · have hzS : z ∈ S := hz0
      have hzV : (z : X) ∈ V ((h : Z → ℂ) z) := hSV ((h : Z → ℂ) z) ⟨z, ⟨hzS, rfl⟩, rfl⟩
      exact Set.indicator_of_mem hzV _
  · intro c _ hc
    exact Set.indicator_of_notMem (fun hzc => hc (hforce c hzc).symm) _
  · intro hnot
    have hz0 : (h : Z → ℂ) z = 0 := by
      by_contra hz0
      exact hnot (hfin.mem_toFinset.mpr ⟨z, hz0, rfl⟩)
    simp only [hz0, Set.indicator_apply, ite_self]

end Surjective

section Transport

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

private theorem comp_homeomorph_mem (σ : X ≃ₜ X') {f : X' → ℂ} (hf : f ∈ testSpace X') : f ∘ σ ∈ testSpace X :=
  ⟨(isLocallyConstant_of_mem hf).comp_continuous σ.continuous, (hasCompactSupport_of_mem hf).comp_homeomorph σ⟩

private def comapHomeomorph (σ : X ≃ₜ X') : testSpace X' ≃ₗ[ℂ] testSpace X where
  toFun f := ⟨(f : X' → ℂ) ∘ σ, comp_homeomorph_mem σ f.2⟩
  invFun g := ⟨(g : X → ℂ) ∘ σ.symm, comp_homeomorph_mem σ.symm g.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)
  left_inv f := Subtype.ext (funext fun x => by
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply])
  right_inv g := Subtype.ext (funext fun x => by
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply])

private theorem comapHomeomorph_apply (σ : X ≃ₜ X') (f : testSpace X') (x : X) :
    (comapHomeomorph σ f : X → ℂ) x = (f : X' → ℂ) (σ x) :=
  rfl

private theorem comapHomeomorph_symm_apply (σ : X ≃ₜ X') (g : testSpace X) (x' : X') :
    ((comapHomeomorph σ).symm g : X' → ℂ) x' = (g : X → ℂ) (σ.symm x') :=
  rfl

end Transport

end SchwartzBruhatSpace

end

end

section

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatIntegral

section Invariance

variable {H : Type*} [AddCommGroup H]

private def IsInvariantUnder (B : AddSubgroup H) (f : H → ℂ) : Prop :=
  ∀ b ∈ B, ∀ x : H, f (x + b) = f x

private theorem IsInvariantUnder.mono {B B' : AddSubgroup H} (h : B' ≤ B) {f : H → ℂ}
    (hf : IsInvariantUnder B f) : IsInvariantUnder B' f :=
  fun b hb x => hf b (h hb) x

private theorem isInvariantUnder_zero (B : AddSubgroup H) : IsInvariantUnder B (0 : H → ℂ) :=
  fun _ _ _ => rfl

private theorem IsInvariantUnder.add {B : AddSubgroup H} {f g : H → ℂ} (hf : IsInvariantUnder B f)
    (hg : IsInvariantUnder B g) : IsInvariantUnder B (f + g) := by
  intro b hb x
  simp only [Pi.add_apply, hf b hb x, hg b hb x]

private theorem IsInvariantUnder.smul {B : AddSubgroup H} (c : ℂ) {f : H → ℂ}
    (hf : IsInvariantUnder B f) : IsInvariantUnder B (c • f) := by
  intro b hb x
  simp only [Pi.smul_apply, hf b hb x]

private theorem IsInvariantUnder.mul {B : AddSubgroup H} {f g : H → ℂ} (hf : IsInvariantUnder B f)
    (hg : IsInvariantUnder B g) : IsInvariantUnder B (f * g) := by
  intro b hb x
  simp only [Pi.mul_apply, hf b hb x, hg b hb x]

private theorem IsInvariantUnder.translate {B : AddSubgroup H} {f : H → ℂ} (hf : IsInvariantUnder B f)
    (a : H) : IsInvariantUnder B (fun x => f (x + a)) := by
  intro b hb x
  show f (x + b + a) = f (x + a)
  rw [add_right_comm, hf b hb]

private theorem IsInvariantUnder.eq_of_mk_eq {B : AddSubgroup H} {f : H → ℂ} (hf : IsInvariantUnder B f)
    {x y : H} (hxy : (x : H ⧸ B) = (y : H ⧸ B)) : f x = f y := by
  rw [QuotientAddGroup.eq] at hxy
  have hy : y = x + (-x + y) := by abel
  rw [hy, hf _ hxy x]

private def descend (B : AddSubgroup H) (f : H → ℂ) (hf : IsInvariantUnder B f) : H ⧸ B → ℂ :=
  fun q => Quotient.liftOn' q f (fun _ _ hxy => hf.eq_of_mk_eq (Quotient.sound' hxy))

@[scoped simp] private theorem descend_mk (B : AddSubgroup H) (f : H → ℂ) (hf : IsInvariantUnder B f) (x : H) :
    descend B f hf (x : H ⧸ B) = f x :=
  rfl

private theorem descend_zero (B : AddSubgroup H) : descend B 0 (isInvariantUnder_zero B) = 0 := by
  funext q
  induction q using QuotientAddGroup.induction_on with
  | H x => simp

private def cosetSum (B : AddSubgroup H) (f : H → ℂ) (hf : IsInvariantUnder B f) : ℂ :=
  ∑ᶠ q : H ⧸ B, descend B f hf q

private def haarIntegralOn (B₀ B : AddSubgroup H) (f : H → ℂ) (hf : IsInvariantUnder B f) : ℂ :=
  ((B.relIndex B₀ : ℕ) : ℂ)⁻¹ * cosetSum B f hf

private theorem haarIntegralOn_zero (B₀ B : AddSubgroup H) :
    haarIntegralOn B₀ B 0 (isInvariantUnder_zero B) = 0 := by
  simp [haarIntegralOn, cosetSum, descend_zero]

end Invariance

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

noncomputable section

open Function

namespace SchwartzBruhatIntegral

section FiniteSupport

variable {H : Type*} [AddCommGroup H]

private theorem support_descend_subset (B : AddSubgroup H) (f : H → ℂ) (hf : IsInvariantUnder B f) :
    support (descend B f hf) ⊆ (QuotientAddGroup.mk : H → H ⧸ B) '' support f := by
  intro q hq
  refine QuotientAddGroup.induction_on q (fun x hx => ?_) hq
  exact ⟨x, hx, rfl⟩

variable [TopologicalSpace H]

private theorem continuous_quotient_mk_addSubgroup (B : AddSubgroup H) :
    Continuous (QuotientAddGroup.mk : H → H ⧸ B) :=
  QuotientAddGroup.continuous_mk

variable [IsTopologicalAddGroup H]

private theorem finite_support_descend (B : AddSubgroup H) (hB : IsOpen (B : Set H)) {f : H → ℂ}
    (hfc : HasCompactSupport f) (hf : IsInvariantUnder B f) :
    (support (descend B f hf)).Finite := by
  haveI : DiscreteTopology (H ⧸ B) := QuotientAddGroup.discreteTopology hB
  have hK : IsCompact (tsupport f) := hfc
  have himage : IsCompact ((QuotientAddGroup.mk : H → H ⧸ B) '' tsupport f) :=
    hK.image (continuous_quotient_mk_addSubgroup B)
  refine himage.finite_of_discrete.subset ?_
  exact (support_descend_subset B f hf).trans (Set.image_mono (subset_tsupport f))

end FiniteSupport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Refinement

variable {H : Type*} [AddCommGroup H]

private theorem quotientEquivProdOfLE_fst_mk {B' B : AddSubgroup H} (h : B' ≤ B) (x : H) :
    ((AddSubgroup.quotientEquivProdOfLE h) (x : H ⧸ B')).1 = (x : H ⧸ B) :=
  rfl

private theorem descend_eq_descend_fst {B' B : AddSubgroup H} (h : B' ≤ B) {f : H → ℂ}
    (hf : IsInvariantUnder B f) (q' : H ⧸ B') :
    descend B' f (hf.mono h) q' = descend B f hf ((AddSubgroup.quotientEquivProdOfLE h) q').1 := by
  refine QuotientAddGroup.induction_on q' (fun x => ?_)
  rw [quotientEquivProdOfLE_fst_mk h x]
  rfl

private theorem finsum_const_quotient {B' B : AddSubgroup H} [Finite (B ⧸ B'.addSubgroupOf B)] (c : ℂ) :
    (∑ᶠ _t : B ⧸ B'.addSubgroupOf B, c) = (B'.relIndex B : ℂ) * c := by
  cases nonempty_fintype (B ⧸ B'.addSubgroupOf B)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

private theorem cosetSum_eq_of_le {B' B : AddSubgroup H} (h : B' ≤ B) [Finite (B ⧸ B'.addSubgroupOf B)]
    {f : H → ℂ} (hf : IsInvariantUnder B f) (hfin : (support (descend B f hf)).Finite) :
    cosetSum B' f (hf.mono h) = (B'.relIndex B : ℂ) * cosetSum B f hf := by
  have h1 : cosetSum B' f (hf.mono h) =
      ∑ᶠ p : (H ⧸ B) × (B ⧸ B'.addSubgroupOf B), descend B f hf p.1 := by
    unfold cosetSum
    simp_rw [descend_eq_descend_fst h hf]
    exact finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE h)
      (f := fun p : (H ⧸ B) × (B ⧸ B'.addSubgroupOf B) => descend B f hf p.1)
  have hfs : (support (fun p : (H ⧸ B) × (B ⧸ B'.addSubgroupOf B) => descend B f hf p.1)).Finite := by
    refine (hfin.prod (Set.finite_univ : (Set.univ : Set (B ⧸ B'.addSubgroupOf B)).Finite)).subset ?_
    intro p hp
    exact ⟨hp, Set.mem_univ _⟩
  rw [h1, finsum_curry _ hfs]
  dsimp only
  simp_rw [finsum_const_quotient]
  rw [cosetSum, mul_finsum]

private theorem haarIntegralOn_eq_of_le {B₀ B B' : AddSubgroup H} (h' : B' ≤ B) (h : B ≤ B₀)
    (hne : B'.relIndex B ≠ 0) {f : H → ℂ} (hf : IsInvariantUnder B f)
    (hfin : (support (descend B f hf)).Finite) :
    haarIntegralOn B₀ B' f (hf.mono h') = haarIntegralOn B₀ B f hf := by
  haveI : Finite (B ⧸ B'.addSubgroupOf B) := AddSubgroup.index_ne_zero_iff_finite.mp hne
  have hc : (B'.relIndex B : ℂ) ≠ 0 := by exact_mod_cast hne
  unfold haarIntegralOn
  rw [cosetSum_eq_of_le h' hf hfin, ← AddSubgroup.relIndex_mul_relIndex B' B B₀ h' h]
  push_cast
  rw [mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hc, one_mul]

end Refinement
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

open Set Function

namespace Localisation

variable {X Y ι : Type*} (φ : X → Y) (A : ι → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (S : Submodule ℂ (X → ℂ))

section Algebra

private noncomputable def coinvariants : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ i : ι, ∃ f ∈ S, A i f - f = g}

private theorem sub_mem_coinvariants (i : ι) {f : X → ℂ} (hf : f ∈ S) : A i f - f ∈ coinvariants A S :=
  Submodule.subset_span ⟨i, f, hf, rfl⟩

private theorem coinvariants_le (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S) : coinvariants A S ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro g ⟨i, f, hf, rfl⟩
  exact S.sub_mem (hAS i f hf) hf

private theorem apply_eq_zero_of_mem_coinvariants (T : (X → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : ι, ∀ f ∈ S, T (A i f) = T f) {g : X → ℂ} (hg : g ∈ coinvariants A S) : T g = 0 := by
  unfold coinvariants at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨i, f, hf, rfl⟩ := hg
    rw [map_sub, hT i f hf, sub_self]
  | zero => exact map_zero T
  | add g₁ g₂ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  | smul c g _ ih => rw [map_smul, ih, smul_zero]

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Multipliers

variable [TopologicalSpace Y]

private theorem indicator_preimage_mem_coinvariants
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    {V : Set Y} (hV : IsClopen V) {n : X → ℂ} (hn : n ∈ coinvariants A S) :
    (φ ⁻¹' V).indicator n ∈ coinvariants A S := by
  unfold coinvariants at hn
  induction hn using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨i, f, hf, rfl⟩ := hg
    rw [Set.indicator_sub', ← hA i V hV f hf]
    exact sub_mem_coinvariants A S i (hS₃ f hf V hV)
  | zero =>
    rw [Set.indicator_zero']
    exact (coinvariants A S).zero_mem
  | add g₁ g₂ _ _ ih₁ ih₂ =>
    rw [Set.indicator_add']
    exact (coinvariants A S).add_mem ih₁ ih₂
  | smul c g _ ih =>
    have hsm : (φ ⁻¹' V).indicator (c • g) = c • (φ ⁻¹' V).indicator g := by
      funext x
      by_cases hx : x ∈ φ ⁻¹' V <;> simp [hx]
    rw [hsm]
    exact (coinvariants A S).smul_mem c ih

end Multipliers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Topological

variable [TopologicalSpace X] [TopologicalSpace Y]

private theorem isCompact_image_support (hφ : Continuous φ) {h : X → ℂ} (hloc : IsLocallyConstant h)
    (hcs : HasCompactSupport h) : IsCompact (φ '' support h) := by
  have hclosed : IsClosed (support h) := by
    have hsupp : support h = {x | h x = 0}ᶜ := by
      ext x
      simp [mem_support]
    rw [hsupp]
    exact isClosed_compl_iff.mpr (hloc.isOpen_fiber 0)
  exact ((hasCompactSupport_def.mp hcs).of_isClosed_subset hclosed subset_closure).image hφ

private theorem exists_isClopen_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    {h : X → ℂ} (hloc : IsLocallyConstant h) (hcs : HasCompactSupport h) {y : Y}
    (hy : ∀ x, φ x = y → h x = 0) :
    ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ ∀ x, φ x ∈ V → h x = 0 := by
  have himg : IsClosed (φ '' support h) := (isCompact_image_support φ hφ hloc hcs).isClosed
  have hyU : y ∈ (φ '' support h)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hy x rfl)
  obtain ⟨V, hV, hyV, hVU⟩ := hY y _ himg.isOpen_compl hyU
  refine ⟨V, hV, hyV, fun x hx => ?_⟩
  by_contra hne
  exact hVU hx ⟨x, hne, rfl⟩

private theorem mem_coinvariants_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    {h : X → ℂ} (hh : h ∈ S)
    (hfib : ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → h x = n x) :
    h ∈ coinvariants A S := by
  have hNS : coinvariants A S ≤ S := coinvariants_le A S hAS
  have key : ∀ y : Y, ∃ V : Set Y, IsClopen V ∧ (y ∈ range φ → y ∈ V) ∧
      (φ ⁻¹' V).indicator h ∈ coinvariants A S := by
    intro y
    by_cases hy : y ∈ range φ
    · obtain ⟨n, hn, hxn⟩ := hfib y hy
      have hd : h - n ∈ S := S.sub_mem hh (hNS hn)
      obtain ⟨V, hV, hyV, hV0⟩ := exists_isClopen_of_forall_fibre φ hφ hY (hS₁ _ hd) (hS₂ _ hd)
        (y := y) (fun x hx => by rw [Pi.sub_apply, hxn x hx, sub_self])
      refine ⟨V, hV, fun _ => hyV, ?_⟩
      have hcongr : (φ ⁻¹' V).indicator h = (φ ⁻¹' V).indicator n := by
        refine Set.indicator_congr fun x hx => ?_
        have hx0 := hV0 x hx
        rw [Pi.sub_apply] at hx0
        exact sub_eq_zero.mp hx0
      rw [hcongr]
      exact indicator_preimage_mem_coinvariants φ A S hS₃ hA hV hn
    · refine ⟨∅, isClopen_empty, fun hy' => (hy hy').elim, ?_⟩
      rw [Set.preimage_empty, Set.indicator_empty']
      exact (coinvariants A S).zero_mem
  choose V hVc hVmem hVN using key
  have hcpt : IsCompact (φ '' support h) := isCompact_image_support φ hφ (hS₁ h hh) (hS₂ h hh)
  obtain ⟨b, -, hbfin, hcover⟩ := hcpt.elim_finite_subcover_image (b := φ '' support h) (c := V)
    (fun y _ => (hVc y).isOpen)
    (fun z hz => Set.mem_biUnion hz (hVmem z (Set.image_subset_range φ _ hz)))
  have hunion : ∀ (t : Set Y), t.Finite → (φ ⁻¹' (⋃ y ∈ t, V y)).indicator h ∈ coinvariants A S := by
    intro t ht
    refine Set.Finite.induction_on
      (motive := fun t _ => (φ ⁻¹' (⋃ y ∈ t, V y)).indicator h ∈ coinvariants A S) t ht ?_ ?_
    · beta_reduce
      rw [Set.biUnion_empty, Set.preimage_empty, Set.indicator_empty']
      exact (coinvariants A S).zero_mem
    · intro a s _ hs ih
      rw [Set.biUnion_insert]
      have hWc : IsClopen (⋃ y ∈ s, V y) := hs.isClopen_biUnion fun y _ => hVc y
      have hsplit : φ ⁻¹' (V a ∪ ⋃ y ∈ s, V y) =
          φ ⁻¹' (V a \ ⋃ y ∈ s, V y) ∪ φ ⁻¹' (⋃ y ∈ s, V y) := by
        rw [← Set.preimage_union, Set.diff_union_self]
      rw [hsplit, Set.indicator_union_of_disjoint (Set.disjoint_sdiff_left.preimage φ)]
      refine (coinvariants A S).add_mem ?_ ih
      have hnest : (φ ⁻¹' (V a \ ⋃ y ∈ s, V y)).indicator h =
          (φ ⁻¹' (V a \ ⋃ y ∈ s, V y)).indicator ((φ ⁻¹' V a).indicator h) := by
        rw [Set.indicator_indicator, Set.inter_eq_left.mpr (Set.preimage_mono Set.diff_subset)]
      rw [hnest]
      exact indicator_preimage_mem_coinvariants φ A S hS₃ hA ((hVc a).diff hWc) (hVN a)
  have hfinal := hunion b hbfin
  have hself : (φ ⁻¹' (⋃ y ∈ b, V y)).indicator h = h :=
    Set.indicator_eq_self.mpr fun x hx => hcover ⟨x, hx, rfl⟩
  rwa [hself] at hfinal

private theorem sub_apply_mem_coinvariants_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    (Θ : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hΘS : ∀ f ∈ S, Θ f ∈ S) {f : X → ℂ} (hf : f ∈ S)
    (hfib : ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → (f - Θ f) x = n x) :
    f - Θ f ∈ coinvariants A S :=
  mem_coinvariants_of_forall_fibre φ A S hφ hY hS₁ hS₂ hS₃ hAS hA (S.sub_mem hf (hΘS f hf)) hfib

private theorem apply_eq_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    (Θ : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hΘS : ∀ f ∈ S, Θ f ∈ S)
    (hfib : ∀ f ∈ S, ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → (f - Θ f) x = n x)
    (T : (X → ℂ) →ₗ[ℂ] ℂ) (hT : ∀ i : ι, ∀ f ∈ S, T (A i f) = T f) {f : X → ℂ} (hf : f ∈ S) :
    T (Θ f) = T f := by
  have hmem : f - Θ f ∈ coinvariants A S :=
    sub_apply_mem_coinvariants_of_forall_fibre φ A S hφ hY hS₁ hS₂ hS₃ hAS hA Θ hΘS hf (hfib f hf)
  have h0 := apply_eq_zero_of_mem_coinvariants A S T hT hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

end Topological
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end Localisation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Product

variable (X : Type*) [TopologicalSpace X]

private def sbSubmodule : Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X}

private theorem mem_sbSubmodule {f : X → ℂ} : f ∈ sbSubmodule X ↔ IsSchwartzBruhat f :=
  Iff.rfl

end Product
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Fibrewise

variable {K Y : Type*}

private structure FibrewiseOp (K Y : Type*) where

  coeff : Y → ℂ

  map : Y → K → K

private def FibrewiseOp.toLin (o : FibrewiseOp K Y) : (K × Y → ℂ) →ₗ[ℂ] (K × Y → ℂ) where
  toFun f := fun p => o.coeff p.2 * f (o.map p.2 p.1, p.2)
  map_add' f g := by
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem FibrewiseOp.toLin_apply (o : FibrewiseOp K Y) (f : K × Y → ℂ) (p : K × Y) :
    o.toLin f p = o.coeff p.2 * f (o.map p.2 p.1, p.2) :=
  rfl

private def FibrewiseOp.fibreRelation (o : FibrewiseOp K Y) (y₀ : Y) (g : K → ℂ) : K → ℂ :=
  fun k => o.coeff y₀ * g (o.map y₀ k) - g k

private def tensorIndicator (g : K → ℂ) (V : Set Y) : K × Y → ℂ :=
  fun p => g p.1 * V.indicator (fun _ => (1 : ℂ)) p.2

private theorem tensorIndicator_apply_of_mem (g : K → ℂ) {V : Set Y} {y : Y} (hy : y ∈ V) (k : K) :
    tensorIndicator g V (k, y) = g k := by
  simp [tensorIndicator, Set.indicator_of_mem hy]

private theorem toLin_tensorIndicator_sub_apply (o : FibrewiseOp K Y) (g : K → ℂ) {V : Set Y} {y₀ : Y} (hy : y₀ ∈ V)
    (k : K) : (o.toLin (tensorIndicator g V) - tensorIndicator g V) (k, y₀) = o.fibreRelation y₀ g k := by
  simp only [Pi.sub_apply, FibrewiseOp.toLin_apply, FibrewiseOp.fibreRelation]
  rw [tensorIndicator_apply_of_mem g hy, tensorIndicator_apply_of_mem g hy]

variable [TopologicalSpace K]

private def fibreSpan {ι : Type*} (ops : ι → FibrewiseOp K Y) (y₀ : Y) : Submodule ℂ (K → ℂ) :=
  Submodule.span ℂ {r | ∃ i : ι, ∃ g : K → ℂ, IsSchwartzBruhat g ∧ (ops i).fibreRelation y₀ g = r}

private theorem fibreRelation_mem_fibreSpan {ι : Type*} (ops : ι → FibrewiseOp K Y) (y₀ : Y) (i : ι) {g : K → ℂ}
    (hg : IsSchwartzBruhat g) : (ops i).fibreRelation y₀ g ∈ fibreSpan ops y₀ :=
  Submodule.subset_span ⟨i, g, hg, rfl⟩

variable [TopologicalSpace Y]

private theorem isSchwartzBruhat_tensorIndicator {g : K → ℂ} (hg : IsSchwartzBruhat g) {V : Set Y} (hV : IsClopen V)
    (hVc : IsCompact V) : IsSchwartzBruhat (tensorIndicator g V) := by
  have hind : IsSchwartzBruhat (V.indicator (fun _ => (1 : ℂ))) := IsSchwartzBruhat.indicator_const hV hVc 1
  refine ⟨?_, ?_⟩
  · exact (hg.1.comp_continuous continuous_fst).mul (hind.1.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro' (IsCompact.prod hg.2 hVc) ((isClosed_tsupport g).prod hV.isClosed) ?_
    intro p hp
    by_cases h1 : p.1 ∈ tsupport g
    · have h2 : p.2 ∉ V := fun h2 => hp ⟨h1, h2⟩
      simp [tensorIndicator, Set.indicator_of_notMem h2]
    · have hg0 : g p.1 = 0 := by
        by_contra hne
        exact h1 (subset_tsupport g hne)
      simp [tensorIndicator, hg0]

private theorem exists_mem_coinvariants_of_mem_fibreSpan {ι : Type*} (ops : ι → FibrewiseOp K Y) {y₀ : Y} {V : Set Y}
    (hV : IsClopen V) (hVc : IsCompact V) (hy : y₀ ∈ V) {h : K → ℂ} (hh : h ∈ fibreSpan ops y₀) :
    ∃ n ∈ Localisation.coinvariants (fun i => (ops i).toLin) (sbSubmodule (K × Y)), ∀ k, n (k, y₀) = h k := by
  unfold fibreSpan at hh
  induction hh using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, g, hg, rfl⟩ := hr
    refine ⟨(ops i).toLin (tensorIndicator g V) - tensorIndicator g V, ?_, fun k => ?_⟩
    · exact Localisation.sub_mem_coinvariants _ _ i
        ((mem_sbSubmodule).mpr (isSchwartzBruhat_tensorIndicator hg hV hVc))
    · exact toLin_tensorIndicator_sub_apply (ops i) g hy k
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => rfl⟩
  | add r₁ r₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, hn₁, h₁⟩ := ih₁
    obtain ⟨n₂, hn₂, h₂⟩ := ih₂
    refine ⟨n₁ + n₂, Submodule.add_mem _ hn₁ hn₂, fun k => ?_⟩
    simp only [Pi.add_apply, h₁ k, h₂ k]
  | smul c r _ ih =>
    obtain ⟨n, hn, hnk⟩ := ih
    refine ⟨c • n, Submodule.smul_mem _ c hn, fun k => ?_⟩
    simp only [Pi.smul_apply, hnk k]

private theorem exists_mem_coinvariants_forall_snd_eq {ι : Type*} (ops : ι → FibrewiseOp K Y) {y₀ : Y} {V : Set Y}
    (hV : IsClopen V) (hVc : IsCompact V) (hy : y₀ ∈ V) {h : K × Y → ℂ}
    (hh : (fun k => h (k, y₀)) ∈ fibreSpan ops y₀) :
    ∃ n ∈ Localisation.coinvariants (fun i => (ops i).toLin) (sbSubmodule (K × Y)),
      ∀ p : K × Y, p.2 = y₀ → h p = n p := by
  obtain ⟨n, hn, hnk⟩ := exists_mem_coinvariants_of_mem_fibreSpan ops hV hVc hy hh
  refine ⟨n, hn, ?_⟩
  rintro ⟨k, y⟩ hp
  simp only at hp
  subst hp
  exact (hnk k).symm

end Fibrewise
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Middle

variable {K₁ Y K₂ : Type*}

private def FibrewiseOp.toLinMid (o : FibrewiseOp (K₁ × K₂) Y) : (K₁ × (Y × K₂) → ℂ) →ₗ[ℂ] (K₁ × (Y × K₂) → ℂ) where
  toFun f := fun x => o.coeff x.2.1 * f ((o.map x.2.1 (x.1, x.2.2)).1, (x.2.1, (o.map x.2.1 (x.1, x.2.2)).2))
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem FibrewiseOp.toLinMid_apply (o : FibrewiseOp (K₁ × K₂) Y) (f : K₁ × (Y × K₂) → ℂ) (x : K₁ × (Y × K₂)) :
    o.toLinMid f x = o.coeff x.2.1 * f ((o.map x.2.1 (x.1, x.2.2)).1, (x.2.1, (o.map x.2.1 (x.1, x.2.2)).2)) :=
  rfl

variable [TopologicalSpace K₁] [TopologicalSpace Y] [TopologicalSpace K₂]

private theorem isSchwartzBruhat_comp_homeo {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] {f : X' → ℂ}
    (hf : IsSchwartzBruhat f) (e : X ≃ₜ X') : IsSchwartzBruhat (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

private def midHomeo (K₁ Y K₂ : Type*) [TopologicalSpace K₁] [TopologicalSpace Y] [TopologicalSpace K₂] :
    K₁ × (Y × K₂) ≃ₜ (K₁ × K₂) × Y :=
  ((Homeomorph.refl K₁).prodCongr (Homeomorph.prodComm Y K₂)).trans (Homeomorph.prodAssoc K₁ K₂ Y).symm

private theorem midHomeo_apply (x : K₁ × (Y × K₂)) : midHomeo K₁ Y K₂ x = ((x.1, x.2.2), x.2.1) :=
  rfl

private def tensorMid (g : K₁ × K₂ → ℂ) (V : Set Y) : K₁ × (Y × K₂) → ℂ :=
  tensorIndicator g V ∘ midHomeo K₁ Y K₂

private theorem tensorMid_apply_of_mem (g : K₁ × K₂ → ℂ) {V : Set Y} {y : Y} (hy : y ∈ V) (k₁ : K₁) (k₂ : K₂) :
    tensorMid g V (k₁, (y, k₂)) = g (k₁, k₂) := by
  show tensorIndicator g V ((k₁, k₂), y) = g (k₁, k₂)
  exact tensorIndicator_apply_of_mem g hy (k₁, k₂)

private theorem isSchwartzBruhat_tensorMid {g : K₁ × K₂ → ℂ} (hg : IsSchwartzBruhat g) {V : Set Y} (hV : IsClopen V)
    (hVc : IsCompact V) : IsSchwartzBruhat (tensorMid g V) :=
  isSchwartzBruhat_comp_homeo (isSchwartzBruhat_tensorIndicator hg hV hVc) (midHomeo K₁ Y K₂)

private theorem toLinMid_tensorMid_sub_apply (o : FibrewiseOp (K₁ × K₂) Y) (g : K₁ × K₂ → ℂ) {V : Set Y} {y₀ : Y}
    (hy : y₀ ∈ V) (k₁ : K₁) (k₂ : K₂) :
    (o.toLinMid (tensorMid g V) - tensorMid g V) (k₁, (y₀, k₂)) = o.fibreRelation y₀ g (k₁, k₂) := by
  simp only [Pi.sub_apply, FibrewiseOp.toLinMid_apply, FibrewiseOp.fibreRelation]
  rw [tensorMid_apply_of_mem g hy, tensorMid_apply_of_mem g hy]

private theorem exists_mem_coinvariants_of_mem_fibreSpan_mid {ι : Type*} (ops : ι → FibrewiseOp (K₁ × K₂) Y) {y₀ : Y}
    {V : Set Y} (hV : IsClopen V) (hVc : IsCompact V) (hy : y₀ ∈ V) {h : K₁ × K₂ → ℂ}
    (hh : h ∈ fibreSpan ops y₀) :
    ∃ n ∈ Localisation.coinvariants (fun i => (ops i).toLinMid) (sbSubmodule (K₁ × (Y × K₂))),
      ∀ k₁ k₂, n (k₁, (y₀, k₂)) = h (k₁, k₂) := by
  unfold fibreSpan at hh
  induction hh using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, g, hg, rfl⟩ := hr
    refine ⟨(ops i).toLinMid (tensorMid g V) - tensorMid g V, ?_, fun k₁ k₂ => ?_⟩
    · exact Localisation.sub_mem_coinvariants _ _ i
        ((mem_sbSubmodule).mpr (isSchwartzBruhat_tensorMid hg hV hVc))
    · exact toLinMid_tensorMid_sub_apply (ops i) g hy k₁ k₂
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k₁ k₂ => rfl⟩
  | add r₁ r₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, hn₁, h₁⟩ := ih₁
    obtain ⟨n₂, hn₂, h₂⟩ := ih₂
    refine ⟨n₁ + n₂, Submodule.add_mem _ hn₁ hn₂, fun k₁ k₂ => ?_⟩
    simp only [Pi.add_apply, h₁ k₁ k₂, h₂ k₁ k₂]
  | smul c r _ ih =>
    obtain ⟨n, hn, hnk⟩ := ih
    refine ⟨c • n, Submodule.smul_mem _ c hn, fun k₁ k₂ => ?_⟩
    simp only [Pi.smul_apply, hnk k₁ k₂]

private theorem exists_mem_coinvariants_forall_mid_eq {ι : Type*} (ops : ι → FibrewiseOp (K₁ × K₂) Y) {y₀ : Y}
    {V : Set Y} (hV : IsClopen V) (hVc : IsCompact V) (hy : y₀ ∈ V) {h : K₁ × (Y × K₂) → ℂ}
    (hh : (fun k : K₁ × K₂ => h (k.1, (y₀, k.2))) ∈ fibreSpan ops y₀) :
    ∃ n ∈ Localisation.coinvariants (fun i => (ops i).toLinMid) (sbSubmodule (K₁ × (Y × K₂))),
      ∀ x : K₁ × (Y × K₂), x.2.1 = y₀ → h x = n x := by
  obtain ⟨n, hn, hnk⟩ := exists_mem_coinvariants_of_mem_fibreSpan_mid ops hV hVc hy hh
  refine ⟨n, hn, ?_⟩
  rintro ⟨k₁, y, k₂⟩ hx
  simp only at hx
  subst hx
  exact (hnk k₁ k₂).symm

end Middle
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

section

noncomputable section

open Function Set

namespace SchwartzBruhatIntegral

private structure BallData (H : Type*) [AddCommGroup H] [TopologicalSpace H] where

  ref : AddSubgroup H

  IsBall : AddSubgroup H → Prop
  isBall_ref : IsBall ref
  le_ref : ∀ {B : AddSubgroup H}, IsBall B → B ≤ ref
  isOpen_of_isBall : ∀ {B : AddSubgroup H}, IsBall B → IsOpen (B : Set H)
  relIndex_ne_zero : ∀ {B : AddSubgroup H}, IsBall B → B.relIndex ref ≠ 0
  exists_isBall_le : ∀ {B B' : AddSubgroup H}, IsBall B → IsBall B' → ∃ C, IsBall C ∧ C ≤ B ∧ C ≤ B'
  exists_isBall_subset : ∀ U ∈ nhds (0 : H), ∃ B, IsBall B ∧ (B : Set H) ⊆ U

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] (D : BallData H)

private theorem relIndex_ne_zero_of_le {B C : AddSubgroup H} (hB : D.IsBall B) (hC : D.IsBall C) (hCB : C ≤ B) :
    C.relIndex B ≠ 0 := by
  intro h0
  apply D.relIndex_ne_zero hC
  rw [← AddSubgroup.relIndex_mul_relIndex C B D.ref hCB (D.le_ref hB), h0, zero_mul]

private theorem exists_isBall_le_finset (s : Finset (AddSubgroup H)) (hs : ∀ B ∈ s, D.IsBall B) :
    ∃ C, D.IsBall C ∧ ∀ B ∈ s, C ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨D.ref, D.isBall_ref, fun B hB => absurd hB (Finset.notMem_empty B)⟩
  | insert B s hBs ih =>
    obtain ⟨C, hC, hCs⟩ := ih (fun B' hB' => hs B' (Finset.mem_insert_of_mem hB'))
    obtain ⟨C', hC', hC'C, hC'B⟩ := D.exists_isBall_le hC (hs B (Finset.mem_insert_self B s))
    refine ⟨C', hC', fun B' hB' => ?_⟩
    rcases Finset.mem_insert.mp hB' with rfl | hB'
    · exact hC'B
    · exact hC'C.trans (hCs B' hB')

variable [IsTopologicalAddGroup H]

private theorem exists_isBall_forall_add_mem {U : Set H} (hU : IsOpen U) {x : H} (hx : x ∈ U) :
    ∃ B, D.IsBall B ∧ ∀ b ∈ B, x + b ∈ U := by
  have hmem : (fun b : H => x + b) ⁻¹' U ∈ nhds (0 : H) := by
    refine (hU.preimage (continuous_const.add continuous_id)).mem_nhds ?_
    simpa using hx
  obtain ⟨B, hB, hBU⟩ := D.exists_isBall_subset _ hmem
  exact ⟨B, hB, fun b hb => hBU hb⟩

private theorem exists_isBall_isInvariantUnder {f : H → ℂ} (hloc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ B, D.IsBall B ∧ IsInvariantUnder B f := by
  classical

  have hpt : ∀ x : H, ∃ B, D.IsBall B ∧ ∀ b ∈ B, f (x + b) = f x := fun x =>
    D.exists_isBall_forall_add_mem (hloc.isOpen_fiber (f x)) (show f x = f x from rfl)
  choose Bx hBx hfx using hpt

  let U : H → Set H := fun x => {y | -x + y ∈ Bx x}
  have hUopen : ∀ x, IsOpen (U x) := fun x =>
    (D.isOpen_of_isBall (hBx x)).preimage (continuous_const.add continuous_id)
  have hUmem : ∀ x, x ∈ U x := fun x => by
    show -x + x ∈ Bx x
    rw [neg_add_cancel]
    exact (Bx x).zero_mem
  have hfU : ∀ x, ∀ y ∈ U x, f y = f x := fun x y hy => by
    have hy' : -x + y ∈ Bx x := hy
    have := hfx x _ hy'
    rwa [add_neg_cancel_left] at this
  have hK : IsCompact (tsupport f) := hcs
  obtain ⟨t, -, htcover⟩ := hK.elim_nhds_subcover U (fun x _ => (hUopen x).mem_nhds (hUmem x))
  obtain ⟨B, hB, hBle⟩ := D.exists_isBall_le_finset (t.image Bx) (by
    intro B' hB'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hB'
    exact hBx x)
  refine ⟨B, hB, fun b hb y => ?_⟩
  have hBx' : ∀ x ∈ t, b ∈ Bx x := fun x hx => hBle (Bx x) (Finset.mem_image_of_mem Bx hx) hb

  have hstay : ∀ x ∈ t, y ∈ U x → y + b ∈ U x := fun x hx hy => by
    show -x + (y + b) ∈ Bx x
    rw [← add_assoc]
    exact (Bx x).add_mem hy (hBx' x hx)
  have hback : ∀ x ∈ t, y + b ∈ U x → y ∈ U x := fun x hx hyb => by
    have h1 : -x + (y + b) ∈ Bx x := hyb
    have h2 : -x + y = (-x + (y + b)) + -b := by abel
    show -x + y ∈ Bx x
    rw [h2]
    exact (Bx x).add_mem h1 ((Bx x).neg_mem (hBx' x hx))
  have hzero : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => by
    by_contra hne
    exact hz (subset_tsupport f hne)
  by_cases hy : y ∈ tsupport f
  · obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (htcover hy)
    rw [hfU x _ (hstay x hxt hyx), hfU x y hyx]
  · by_cases hyb : y + b ∈ tsupport f
    · obtain ⟨x, hxt, hybx⟩ := mem_iUnion₂.mp (htcover hyb)
      rw [hfU x _ hybx, hfU x y (hback x hxt hybx)]
    · rw [hzero _ hyb, hzero _ hy]

private theorem exists_isBall_isInvariantUnder_of_isSchwartzBruhat {f : H → ℂ}
    (hf : LanglandsTunnell.TateLocal.IsSchwartzBruhat f) : ∃ B, D.IsBall B ∧ IsInvariantUnder B f :=
  D.exists_isBall_isInvariantUnder hf.1 hf.2

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set

namespace SchwartzBruhatIntegral

section Algebra

variable {H : Type*} [AddCommGroup H]

private theorem descend_add (B : AddSubgroup H) {f g : H → ℂ} (hf : IsInvariantUnder B f) (hg : IsInvariantUnder B g) :
    descend B (f + g) (hf.add hg) = descend B f hf + descend B g hg := by
  funext q
  refine QuotientAddGroup.induction_on q (fun x => ?_)
  rfl

private theorem descend_smul (B : AddSubgroup H) (c : ℂ) {f : H → ℂ} (hf : IsInvariantUnder B f) :
    descend B (c • f) (hf.smul c) = c • descend B f hf := by
  funext q
  refine QuotientAddGroup.induction_on q (fun x => ?_)
  rfl

private theorem cosetSum_add (B : AddSubgroup H) {f g : H → ℂ} (hf : IsInvariantUnder B f) (hg : IsInvariantUnder B g)
    (hfin : (support (descend B f hf)).Finite) (hgin : (support (descend B g hg)).Finite) :
    cosetSum B (f + g) (hf.add hg) = cosetSum B f hf + cosetSum B g hg := by
  unfold cosetSum
  rw [descend_add B hf hg]
  exact finsum_add_distrib hfin hgin

private theorem cosetSum_smul (B : AddSubgroup H) (c : ℂ) {f : H → ℂ} (hf : IsInvariantUnder B f) :
    cosetSum B (c • f) (hf.smul c) = c * cosetSum B f hf := by
  unfold cosetSum
  rw [descend_smul B c hf, mul_finsum]
  rfl

private theorem haarIntegralOn_add (B₀ B : AddSubgroup H) {f g : H → ℂ} (hf : IsInvariantUnder B f)
    (hg : IsInvariantUnder B g) (hfin : (support (descend B f hf)).Finite)
    (hgin : (support (descend B g hg)).Finite) :
    haarIntegralOn B₀ B (f + g) (hf.add hg) = haarIntegralOn B₀ B f hf + haarIntegralOn B₀ B g hg := by
  unfold haarIntegralOn
  rw [cosetSum_add B hf hg hfin hgin, mul_add]

private theorem haarIntegralOn_smul (B₀ B : AddSubgroup H) (c : ℂ) {f : H → ℂ} (hf : IsInvariantUnder B f) :
    haarIntegralOn B₀ B (c • f) (hf.smul c) = c * haarIntegralOn B₀ B f hf := by
  unfold haarIntegralOn
  rw [cosetSum_smul B c hf]
  ring

private theorem descend_translate (B : AddSubgroup H) {f : H → ℂ} (hf : IsInvariantUnder B f) (a : H) (q : H ⧸ B) :
    descend B (fun x => f (x + a)) (hf.translate a) q = descend B f hf (q + (a : H ⧸ B)) := by
  refine QuotientAddGroup.induction_on q (fun x => ?_)
  rfl

private theorem cosetSum_translate (B : AddSubgroup H) {f : H → ℂ} (hf : IsInvariantUnder B f) (a : H) :
    cosetSum B (fun x => f (x + a)) (hf.translate a) = cosetSum B f hf := by
  unfold cosetSum
  simp_rw [descend_translate B hf a]
  have h := finsum_comp_equiv (Equiv.addRight (a : H ⧸ B)) (f := descend B f hf)
  simpa only [Equiv.coe_addRight] using h

private theorem haarIntegralOn_translate (B₀ B : AddSubgroup H) {f : H → ℂ} (hf : IsInvariantUnder B f) (a : H) :
    haarIntegralOn B₀ B (fun x => f (x + a)) (hf.translate a) = haarIntegralOn B₀ B f hf := by
  unfold haarIntegralOn
  rw [cosetSum_translate B hf a]

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)

private def Integrable (f : H → ℂ) : Prop :=
  HasCompactSupport f ∧ ∃ B, D.IsBall B ∧ IsInvariantUnder B f

private theorem integrable_of_isSchwartzBruhat {f : H → ℂ} (hf : LanglandsTunnell.TateLocal.IsSchwartzBruhat f) :
    D.Integrable f :=
  ⟨hf.2, D.exists_isBall_isInvariantUnder hf.1 hf.2⟩

private theorem haarIntegralOn_eq_haarIntegralOn {f : H → ℂ} (hcs : HasCompactSupport f) {B₁ B₂ : AddSubgroup H}
    (h₁ : D.IsBall B₁) (h₂ : D.IsBall B₂) (hf₁ : IsInvariantUnder B₁ f) (hf₂ : IsInvariantUnder B₂ f) :
    haarIntegralOn D.ref B₁ f hf₁ = haarIntegralOn D.ref B₂ f hf₂ := by
  obtain ⟨C, hC, hC₁, hC₂⟩ := D.exists_isBall_le h₁ h₂
  have e₁ := haarIntegralOn_eq_of_le hC₁ (D.le_ref h₁) (D.relIndex_ne_zero_of_le h₁ hC hC₁) hf₁
    (finite_support_descend B₁ (D.isOpen_of_isBall h₁) hcs hf₁)
  have e₂ := haarIntegralOn_eq_of_le hC₂ (D.le_ref h₂) (D.relIndex_ne_zero_of_le h₂ hC hC₂) hf₂
    (finite_support_descend B₂ (D.isOpen_of_isBall h₂) hcs hf₂)
  rw [← e₁, ← e₂]

open Classical in

private def haarIntegral (f : H → ℂ) : ℂ :=
  if h : D.Integrable f then haarIntegralOn D.ref (Classical.choose h.2) f (Classical.choose_spec h.2).2 else 0

private theorem haarIntegral_eq {f : H → ℂ} (hcs : HasCompactSupport f) {B : AddSubgroup H} (hB : D.IsBall B)
    (hf : IsInvariantUnder B f) : D.haarIntegral f = haarIntegralOn D.ref B f hf := by
  have hint : D.Integrable f := ⟨hcs, B, hB, hf⟩
  rw [haarIntegral, dif_pos hint]
  exact D.haarIntegralOn_eq_haarIntegralOn hcs (Classical.choose_spec hint.2).1 hB _ hf

omit [IsTopologicalAddGroup H] in
private theorem haarIntegral_of_not_integrable {f : H → ℂ} (h : ¬ D.Integrable f) : D.haarIntegral f = 0 := by
  rw [haarIntegral, dif_neg h]

private theorem haarIntegral_add {f g : H → ℂ} (hf : D.Integrable f) (hg : D.Integrable g) :
    D.haarIntegral (f + g) = D.haarIntegral f + D.haarIntegral g := by
  obtain ⟨hfc, Bf, hBf, hfB⟩ := hf
  obtain ⟨hgc, Bg, hBg, hgB⟩ := hg
  obtain ⟨C, hC, hCf, hCg⟩ := D.exists_isBall_le hBf hBg
  have hfC : IsInvariantUnder C f := hfB.mono hCf
  have hgC : IsInvariantUnder C g := hgB.mono hCg
  rw [D.haarIntegral_eq (hfc.add hgc) hC (hfC.add hgC), D.haarIntegral_eq hfc hC hfC, D.haarIntegral_eq hgc hC hgC]
  exact haarIntegralOn_add D.ref C hfC hgC (finite_support_descend C (D.isOpen_of_isBall hC) hfc hfC)
    (finite_support_descend C (D.isOpen_of_isBall hC) hgc hgC)

private theorem haarIntegral_smul (c : ℂ) {f : H → ℂ} (hf : D.Integrable f) :
    D.haarIntegral (c • f) = c * D.haarIntegral f := by
  obtain ⟨hfc, B, hB, hfB⟩ := hf
  have hcs : HasCompactSupport (c • f) := hfc.comp_left (g := (c * ·)) (mul_zero c)
  rw [D.haarIntegral_eq hcs hB (hfB.smul c), D.haarIntegral_eq hfc hB hfB]
  exact haarIntegralOn_smul D.ref B c hfB

private theorem haarIntegral_translate {f : H → ℂ} (hf : D.Integrable f) (a : H) :
    D.haarIntegral (fun x => f (x + a)) = D.haarIntegral f := by
  obtain ⟨hfc, B, hB, hfB⟩ := hf
  have hcs : HasCompactSupport (fun x => f (x + a)) := hfc.comp_homeomorph (Homeomorph.addRight a)
  rw [D.haarIntegral_eq hcs hB (hfB.translate a), D.haarIntegral_eq hfc hB hfB]
  exact haarIntegralOn_translate D.ref B hfB a

omit [IsTopologicalAddGroup H] in
private theorem isInvariantUnder_indicator_ref :
    IsInvariantUnder D.ref ((D.ref : Set H).indicator (fun _ => (1 : ℂ))) := by
  intro b hb x
  by_cases hx : x ∈ D.ref
  · have hxb : x + b ∈ D.ref := D.ref.add_mem hx hb
    rw [Set.indicator_of_mem (show x + b ∈ (D.ref : Set H) from hxb),
      Set.indicator_of_mem (show x ∈ (D.ref : Set H) from hx)]
  · have hxb : x + b ∉ D.ref := fun h => hx ((AddSubgroup.add_mem_cancel_right _ hb).mp h)
    rw [Set.indicator_of_notMem (show x + b ∉ (D.ref : Set H) from hxb),
      Set.indicator_of_notMem (show x ∉ (D.ref : Set H) from hx)]

open Classical in
private theorem descend_indicator_ref :
    descend D.ref ((D.ref : Set H).indicator (fun _ => (1 : ℂ))) D.isInvariantUnder_indicator_ref =
      fun q => if q = 0 then (1 : ℂ) else 0 := by
  funext q
  refine QuotientAddGroup.induction_on q (fun x => ?_)
  show (D.ref : Set H).indicator (fun _ => (1 : ℂ)) x = if ((x : H ⧸ D.ref) = 0) then (1 : ℂ) else 0
  by_cases hx : x ∈ D.ref
  · rw [Set.indicator_of_mem (show x ∈ (D.ref : Set H) from hx), if_pos ((QuotientAddGroup.eq_zero_iff x).mpr hx)]
  · rw [Set.indicator_of_notMem (show x ∉ (D.ref : Set H) from hx),
      if_neg (fun h => hx ((QuotientAddGroup.eq_zero_iff x).mp h))]

private theorem haarIntegral_indicator_ref (hc : IsCompact (D.ref : Set H)) :
    D.haarIntegral ((D.ref : Set H).indicator (fun _ => (1 : ℂ))) = 1 := by
  have hclosed : IsClosed (D.ref : Set H) := D.ref.isClosed_of_isOpen (D.isOpen_of_isBall D.isBall_ref)
  have hcs : HasCompactSupport ((D.ref : Set H).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro' hc hclosed (fun x hx => Set.indicator_of_notMem hx _)
  rw [D.haarIntegral_eq hcs D.isBall_ref D.isInvariantUnder_indicator_ref]
  unfold haarIntegralOn cosetSum
  rw [descend_indicator_ref, AddSubgroup.relIndex_self, finsum_eq_single _ (0 : H ⧸ D.ref)]
  · simp
  · intro q hq
    simp [hq]

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Relations

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H]

private def translationSpan (H : Type*) [AddCommGroup H] [TopologicalSpace H] : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ {r | ∃ a : H, ∃ g : H → ℂ, IsSchwartzBruhat g ∧ (fun x => g (x + a)) - g = r}

private theorem translate_sub_mem_translationSpan {g : H → ℂ} (hg : IsSchwartzBruhat g) (a : H) :
    (fun x => g (x + a)) - g ∈ translationSpan H :=
  Submodule.subset_span ⟨a, g, hg, rfl⟩

end Relations
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)

private theorem isCompact_of_isBall (hc : IsCompact (D.ref : Set H)) {B : AddSubgroup H} (hB : D.IsBall B) :
    IsCompact (B : Set H) :=
  hc.of_isClosed_subset (B.isClosed_of_isOpen (D.isOpen_of_isBall hB)) (D.le_ref hB)

private theorem isSchwartzBruhat_indicator_of_isBall (hc : IsCompact (D.ref : Set H)) {B : AddSubgroup H}
    (hB : D.IsBall B) (c : ℂ) : IsSchwartzBruhat ((B : Set H).indicator (fun _ => c)) :=
  IsSchwartzBruhat.indicator_const
    ⟨B.isClosed_of_isOpen (D.isOpen_of_isBall hB), D.isOpen_of_isBall hB⟩ (D.isCompact_of_isBall hc hB) c

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Cosets

variable {H : Type*} [AddCommGroup H] (B : AddSubgroup H)

open Classical in

private theorem indicator_add_eq (a x : H) :
    (B : Set H).indicator (fun _ => (1 : ℂ)) (x + a) = if ((x : H ⧸ B) = ((-a : H) : H ⧸ B)) then 1 else 0 := by
  have key : x + a ∈ B ↔ ((x : H ⧸ B) = ((-a : H) : H ⧸ B)) := by
    rw [QuotientAddGroup.eq]
    constructor
    · intro h
      have h' : -x + -a = -(x + a) := by abel
      rw [h']
      exact B.neg_mem h
    · intro h
      have h' : x + a = -(-x + -a) := by abel
      rw [h']
      exact B.neg_mem h
  by_cases hx : x + a ∈ B
  · rw [Set.indicator_of_mem (show x + a ∈ (B : Set H) from hx), if_pos (key.mp hx)]
  · rw [Set.indicator_of_notMem (show x + a ∉ (B : Set H) from hx), if_neg (fun h => hx (key.mpr h))]

open Classical in

private def cosetIndicator (q : H ⧸ B) : H → ℂ :=
  fun x => if ((x : H ⧸ B) = q) then 1 else 0

open Classical in
private theorem cosetIndicator_eq_translate (q : H ⧸ B) :
    cosetIndicator B q = fun x => (B : Set H).indicator (fun _ => (1 : ℂ)) (x + -(Quotient.out q)) := by
  funext x
  show (if ((x : H ⧸ B) = q) then (1 : ℂ) else 0) = (B : Set H).indicator (fun _ => (1 : ℂ)) (x + -(Quotient.out q))
  rw [indicator_add_eq B (-(Quotient.out q)) x, neg_neg, QuotientAddGroup.out_eq' q]

private theorem eq_sum_cosetIndicator {f : H → ℂ} (hf : IsInvariantUnder B f)
    (hfin : (support (descend B f hf)).Finite) :
    f = ∑ q ∈ hfin.toFinset, descend B f hf q • cosetIndicator B q := by
  classical
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, cosetIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq hfin.toFinset (x : H ⧸ B) (descend B f hf)]
  by_cases hx : (x : H ⧸ B) ∈ hfin.toFinset
  · rw [if_pos hx, descend_mk]
  · rw [if_neg hx]
    have hx' : descend B f hf (x : H ⧸ B) = 0 := by
      by_contra hne
      exact hx (hfin.mem_toFinset.mpr hne)
    rw [descend_mk] at hx'
    exact hx'

end Cosets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)

private theorem cosetIndicator_sub_mem (hc : IsCompact (D.ref : Set H)) {B : AddSubgroup H} (hB : D.IsBall B)
    (q : H ⧸ B) : cosetIndicator B q - (B : Set H).indicator (fun _ => (1 : ℂ)) ∈ translationSpan H := by
  rw [cosetIndicator_eq_translate]
  exact translate_sub_mem_translationSpan (D.isSchwartzBruhat_indicator_of_isBall hc hB 1) _

omit [TopologicalSpace H] in
private theorem cosetSum_eq_sum {B : AddSubgroup H} {f : H → ℂ} (hf : IsInvariantUnder B f)
    (hfin : (support (descend B f hf)).Finite) :
    cosetSum B f hf = ∑ q ∈ hfin.toFinset, descend B f hf q := by
  unfold cosetSum
  exact finsum_eq_finsetSum_of_support_subset _ (fun q hq => hfin.mem_toFinset.mpr hq)

private theorem cosetSum_eq_zero_of_haarIntegral_eq_zero {f : H → ℂ} (hcs : HasCompactSupport f) {B : AddSubgroup H}
    (hB : D.IsBall B) (hf : IsInvariantUnder B f) (h0 : D.haarIntegral f = 0) : cosetSum B f hf = 0 := by
  rw [D.haarIntegral_eq hcs hB hf] at h0
  unfold haarIntegralOn at h0
  have hne : ((B.relIndex D.ref : ℕ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast D.relIndex_ne_zero hB)
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hne
  · exact h

private theorem mem_translationSpan_of_haarIntegral_eq_zero (hc : IsCompact (D.ref : Set H)) {f : H → ℂ}
    (hf : IsSchwartzBruhat f) (h0 : D.haarIntegral f = 0) : f ∈ translationSpan H := by
  classical
  obtain ⟨B, hB, hfB⟩ := D.exists_isBall_isInvariantUnder hf.1 hf.2
  have hfin : (support (descend B f hfB)).Finite := finite_support_descend B (D.isOpen_of_isBall hB) hf.2 hfB
  set ind : H → ℂ := (B : Set H).indicator (fun _ => (1 : ℂ)) with hind
  have hsum : cosetSum B f hfB = 0 := D.cosetSum_eq_zero_of_haarIntegral_eq_zero hf.2 hB hfB h0
  rw [cosetSum_eq_sum hfB hfin] at hsum
  have hdecomp := eq_sum_cosetIndicator B hfB hfin
  have hsplit : (∑ q ∈ hfin.toFinset, descend B f hfB q • cosetIndicator B q) =
      (∑ q ∈ hfin.toFinset, descend B f hfB q • (cosetIndicator B q - ind)) +
        (∑ q ∈ hfin.toFinset, descend B f hfB q) • ind := by
    rw [Finset.sum_smul]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hdecomp, hsplit, hsum, zero_smul, add_zero]
  refine Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ ?_)
  exact D.cosetIndicator_sub_mem hc hB q

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Character

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] (χ : AddChar H ℂ)

omit [TopologicalSpace H] in
private theorem addChar_ne_zero (x : H) : χ x ≠ 0 := by
  intro h
  have h1 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

private theorem isLocallyConstant_inv (hχ : IsLocallyConstant (fun x : H => χ x)) :
    IsLocallyConstant (fun x : H => (χ x)⁻¹) :=
  hχ.comp (fun z : ℂ => z⁻¹)

private theorem isSchwartzBruhat_mul_char {f : H → ℂ} (hf : IsSchwartzBruhat f)
    (hχ : IsLocallyConstant (fun x : H => χ x)) : IsSchwartzBruhat (fun x => f x * χ x) :=
  ⟨hf.1.mul hχ, hf.2.mul_right⟩

private theorem isSchwartzBruhat_mul_char_inv {f : H → ℂ} (hf : IsSchwartzBruhat f)
    (hχ : IsLocallyConstant (fun x : H => χ x)) : IsSchwartzBruhat (fun x => f x * (χ x)⁻¹) :=
  ⟨hf.1.mul (isLocallyConstant_inv χ hχ), hf.2.mul_right⟩

private def twistedSpan : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ
    {r | ∃ a : H, ∃ g : H → ℂ, IsSchwartzBruhat g ∧ (fun x => g (x + a)) - (χ a)⁻¹ • g = r}

private theorem translate_sub_smul_mem_twistedSpan {g : H → ℂ} (hg : IsSchwartzBruhat g) (a : H) :
    (fun x => g (x + a)) - (χ a)⁻¹ • g ∈ twistedSpan χ :=
  Submodule.subset_span ⟨a, g, hg, rfl⟩

private theorem mul_char_inv_translate_sub {g : H → ℂ} (a : H) :
    (fun x => ((fun y => g (y + a)) - g) x * (χ x)⁻¹) =
      χ a • ((fun x => (fun y => g y * (χ y)⁻¹) (x + a)) - (χ a)⁻¹ • fun y => g y * (χ y)⁻¹) := by
  funext x
  have hxa : χ (x + a) = χ x * χ a := AddChar.map_add_eq_mul χ x a
  have hx : χ x ≠ 0 := addChar_ne_zero χ x
  have ha : χ a ≠ 0 := addChar_ne_zero χ a
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxa]
  field_simp

private theorem mul_char_inv_mem_twistedSpan (hχ : IsLocallyConstant (fun x : H => χ x)) {r : H → ℂ}
    (hr : r ∈ translationSpan H) : (fun x => r x * (χ x)⁻¹) ∈ twistedSpan χ := by
  unfold translationSpan at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨a, g, hg, rfl⟩ := hr
    rw [mul_char_inv_translate_sub χ a]
    exact (twistedSpan χ).smul_mem _
      (translate_sub_smul_mem_twistedSpan χ (isSchwartzBruhat_mul_char_inv χ hg hχ) a)
  | zero =>
    have h0 : (fun x => (0 : H → ℂ) x * (χ x)⁻¹) = (0 : H → ℂ) := by
      funext x
      simp
    rw [h0]
    exact (twistedSpan χ).zero_mem
  | add r₁ r₂ _ _ ih₁ ih₂ =>
    have : (fun x => (r₁ + r₂) x * (χ x)⁻¹) = (fun x => r₁ x * (χ x)⁻¹) + fun x => r₂ x * (χ x)⁻¹ := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [this]
    exact (twistedSpan χ).add_mem ih₁ ih₂
  | smul c r _ ih =>
    have : (fun x => (c • r) x * (χ x)⁻¹) = c • fun x => r x * (χ x)⁻¹ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact (twistedSpan χ).smul_mem c ih

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)
  (χ : AddChar H ℂ)

private def twistedIntegral (f : H → ℂ) : ℂ :=
  D.haarIntegral (fun x => f x * χ x)

private theorem mem_twistedSpan_of_twistedIntegral_eq_zero (hc : IsCompact (D.ref : Set H))
    (hχ : IsLocallyConstant (fun x : H => χ x)) {f : H → ℂ} (hf : IsSchwartzBruhat f)
    (h0 : D.twistedIntegral χ f = 0) : f ∈ twistedSpan χ := by
  have hmem : (fun x => f x * χ x) ∈ translationSpan H :=
    D.mem_translationSpan_of_haarIntegral_eq_zero hc (isSchwartzBruhat_mul_char χ hf hχ) h0
  have key := mul_char_inv_mem_twistedSpan χ hχ hmem
  have hfeq : (fun x => (fun y => f y * χ y) x * (χ x)⁻¹) = f := by
    funext x
    have hx : χ x ≠ 0 := addChar_ne_zero χ x
    field_simp
  rwa [hfeq] at key

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Comap

variable {H : Type*} [AddCommGroup H] (B : AddSubgroup H) (e : H ≃+ H)

private theorem isInvariantUnder_comap {f : H → ℂ} (hf : IsInvariantUnder B f) :
    IsInvariantUnder (B.comap e.toAddMonoidHom) (fun x => f (e x)) := by
  intro b hb x
  have hb' : e b ∈ B := hb
  show f (e (x + b)) = f (e x)
  rw [map_add]
  exact hf (e b) hb' (e x)

private def quotientCongr : H ⧸ B.comap e.toAddMonoidHom ≃+ H ⧸ B :=
  QuotientAddGroup.congr (B.comap e.toAddMonoidHom) B e
    (AddSubgroup.map_comap_eq_self_of_surjective (f := e.toAddMonoidHom) e.surjective B)

private
theorem quotientCongr_mk (x : H) : quotientCongr B e (x : H ⧸ B.comap e.toAddMonoidHom) = ((e x : H) : H ⧸ B) :=
  rfl

private theorem descend_comap {f : H → ℂ} (hf : IsInvariantUnder B f) (q : H ⧸ B.comap e.toAddMonoidHom) :
    descend (B.comap e.toAddMonoidHom) (fun x => f (e x)) (isInvariantUnder_comap B e hf) q =
      descend B f hf (quotientCongr B e q) := by
  refine QuotientAddGroup.induction_on q (fun x => ?_)
  rw [quotientCongr_mk]
  rfl

private theorem cosetSum_comap {f : H → ℂ} (hf : IsInvariantUnder B f) :
    cosetSum (B.comap e.toAddMonoidHom) (fun x => f (e x)) (isInvariantUnder_comap B e hf) = cosetSum B f hf := by
  unfold cosetSum
  simp_rw [descend_comap B e hf]
  exact finsum_comp_equiv (quotientCongr B e).toEquiv

private theorem relIndex_comap_of_map_eq {R : AddSubgroup H} (hR : R.map e.toAddMonoidHom = R) :
    (B.comap e.toAddMonoidHom).relIndex R = B.relIndex R := by
  rw [AddSubgroup.relIndex_comap, hR]

private theorem haarIntegralOn_comap {R : AddSubgroup H} (hR : R.map e.toAddMonoidHom = R) {f : H → ℂ}
    (hf : IsInvariantUnder B f) :
    haarIntegralOn R (B.comap e.toAddMonoidHom) (fun x => f (e x)) (isInvariantUnder_comap B e hf) =
      haarIntegralOn R B f hf := by
  unfold haarIntegralOn
  rw [cosetSum_comap B e hf, relIndex_comap_of_map_eq B e hR]

end Comap
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)

private structure IsAdmissibleAut (e : H ≃+ H) : Prop where
  continuous_toFun : Continuous e
  continuous_invFun : Continuous e.symm
  map_ref : D.ref.map e.toAddMonoidHom = D.ref
  isBall_comap : ∀ {B : AddSubgroup H}, D.IsBall B → D.IsBall (B.comap e.toAddMonoidHom)

variable {D}

private def IsAdmissibleAut.homeo {e : H ≃+ H} (he : D.IsAdmissibleAut e) : H ≃ₜ H :=
  ⟨e.toEquiv, he.continuous_toFun, he.continuous_invFun⟩

omit [IsTopologicalAddGroup H] in
private theorem IsAdmissibleAut.hasCompactSupport_comp {e : H ≃+ H} (he : D.IsAdmissibleAut e) {f : H → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (fun x => f (e x)) :=
  hf.comp_homeomorph he.homeo

private theorem IsAdmissibleAut.integrable_comp {e : H ≃+ H} (he : D.IsAdmissibleAut e) {f : H → ℂ}
    (hf : D.Integrable f) : D.Integrable (fun x => f (e x)) := by
  obtain ⟨hfc, B, hB, hfB⟩ := hf
  exact ⟨he.hasCompactSupport_comp hfc, B.comap e.toAddMonoidHom, he.isBall_comap hB,
    isInvariantUnder_comap B e hfB⟩

variable (D)

private theorem haarIntegral_comp {e : H ≃+ H} (he : D.IsAdmissibleAut e) {f : H → ℂ} (hf : D.Integrable f) :
    D.haarIntegral (fun x => f (e x)) = D.haarIntegral f := by
  obtain ⟨hfc, B, hB, hfB⟩ := hf
  rw [D.haarIntegral_eq (he.hasCompactSupport_comp hfc) (he.isBall_comap hB) (isInvariantUnder_comap B e hfB),
    D.haarIntegral_eq hfc hB hfB]
  exact haarIntegralOn_comap B e he.map_ref hfB

private theorem twistedIntegral_comp (χ : AddChar H ℂ) {e : H ≃+ H} (he : D.IsAdmissibleAut e)
    (hχ : IsLocallyConstant (fun x : H => χ x)) {f : H → ℂ} (hf : IsSchwartzBruhat f) :
    D.twistedIntegral χ (fun x => f (e x)) =
      D.twistedIntegral (χ.compAddMonoidHom e.symm.toAddMonoidHom) f := by
  unfold twistedIntegral
  have hg : IsSchwartzBruhat (fun y => f y * χ (e.symm y)) := by
    refine ⟨hf.1.mul (hχ.comp_continuous he.continuous_invFun), hf.2.mul_right⟩
  have hkey : (fun x => f (e x) * χ x) = fun x => (fun y => f y * χ (e.symm y)) (e x) := by
    funext x
    simp only [AddEquiv.symm_apply_apply]
  rw [hkey, D.haarIntegral_comp he (D.integrable_of_isSchwartzBruhat hg)]
  rfl

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Relations

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (χ : AddChar H ℂ)

private def twistedRel (a : H) (g : H → ℂ) : H → ℂ :=
  (fun x => g (x + a)) - (χ a)⁻¹ • g

omit [IsTopologicalAddGroup H] in
private theorem twistedRel_mem_twistedSpan {g : H → ℂ} (hg : IsSchwartzBruhat g) (a : H) :
    twistedRel χ a g ∈ twistedSpan χ :=
  translate_sub_smul_mem_twistedSpan χ hg a

omit [TopologicalSpace H] in
private theorem twistedRel_zero (g : H → ℂ) : twistedRel χ 0 g = 0 := by
  funext x
  simp [twistedRel, AddChar.map_zero_eq_one]

private theorem isSchwartzBruhat_translate {g : H → ℂ} (hg : IsSchwartzBruhat g) (a : H) :
    IsSchwartzBruhat (fun x => g (x + a)) :=
  ⟨hg.1.comp_continuous (continuous_id.add continuous_const), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩

omit [IsTopologicalAddGroup H] in

private theorem twistedRel_add (g : H → ℂ) (a a' : H) :
    twistedRel χ (a + a') g = twistedRel χ a' (fun x => g (x + a)) + (χ a')⁻¹ • twistedRel χ a g := by
  funext x
  have ha : χ a ≠ 0 := addChar_ne_zero χ a
  have ha' : χ a' ≠ 0 := addChar_ne_zero χ a'
  have hx : x + a' + a = x + (a + a') := by
    rw [add_assoc, add_comm a' a]
  simp only [twistedRel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul, hx]
  field_simp
  ring

private def relationClosed (M : Submodule ℂ (H → ℂ)) : AddSubmonoid H where
  carrier := {a | ∀ g : H → ℂ, IsSchwartzBruhat g → twistedRel χ a g ∈ M}
  zero_mem' := by
    intro g _
    rw [twistedRel_zero]
    exact M.zero_mem
  add_mem' := by
    intro a a' ha ha' g hg
    rw [twistedRel_add χ g a a']
    exact M.add_mem (ha' _ (isSchwartzBruhat_translate hg a)) (M.smul_mem _ (ha g hg))

private theorem mem_relationClosed_iff (M : Submodule ℂ (H → ℂ)) (a : H) :
    a ∈ relationClosed χ M ↔ ∀ g : H → ℂ, IsSchwartzBruhat g → twistedRel χ a g ∈ M :=
  Iff.rfl

private theorem twistedSpan_le_of_relationClosed_eq_top {M : Submodule ℂ (H → ℂ)} (h : relationClosed χ M = ⊤) :
    twistedSpan χ ≤ M := by
  unfold twistedSpan
  rw [Submodule.span_le]
  rintro r ⟨a, g, hg, rfl⟩
  have ha : a ∈ relationClosed χ M := by
    rw [h]
    exact AddSubmonoid.mem_top a
  exact ha g hg

private theorem twistedSpan_le_of_closure {M : Submodule ℂ (H → ℂ)} (s : Set H) (hs : AddSubmonoid.closure s = ⊤)
    (h : ∀ a ∈ s, ∀ g : H → ℂ, IsSchwartzBruhat g → twistedRel χ a g ∈ M) : twistedSpan χ ≤ M := by
  refine twistedSpan_le_of_relationClosed_eq_top χ ?_
  rw [eq_top_iff, ← hs, AddSubmonoid.closure_le]
  intro a ha
  exact h a ha

end Relations
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Axes

variable {H₁ H₂ : Type*} [AddCommGroup H₁] [TopologicalSpace H₁] [IsTopologicalAddGroup H₁] [AddCommGroup H₂]
  [TopologicalSpace H₂] [IsTopologicalAddGroup H₂]

omit [TopologicalSpace H₁] in
private theorem closure_axes_eq_top :
    AddSubmonoid.closure ((range fun a : H₁ => ((a, 0) : H₁ × H₂)) ∪ range fun b : H₂ => ((0, b) : H₁ × H₂)) =
      ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have h : ((a, b) : H₁ × H₂) = (a, 0) + (0, b) := by
    ext <;> simp
  rw [h]
  exact AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure (Or.inl ⟨a, rfl⟩))
    (AddSubmonoid.subset_closure (Or.inr ⟨b, rfl⟩))

private theorem twistedSpan_le_of_axes (χ : AddChar (H₁ × H₂) ℂ) {M : Submodule ℂ (H₁ × H₂ → ℂ)}
    (h₁ : ∀ a : H₁, ∀ g : H₁ × H₂ → ℂ, IsSchwartzBruhat g → twistedRel χ (a, 0) g ∈ M)
    (h₂ : ∀ b : H₂, ∀ g : H₁ × H₂ → ℂ, IsSchwartzBruhat g → twistedRel χ (0, b) g ∈ M) : twistedSpan χ ≤ M := by
  refine twistedSpan_le_of_closure χ _ closure_axes_eq_top ?_
  rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · exact h₁ a
  · exact h₂ b

end Axes
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (D : BallData H)
  (χ : AddChar H ℂ)

private theorem twistedIntegral_sub_smul (hχ : IsLocallyConstant (fun x : H => χ x)) {g m : H → ℂ}
    (hg : IsSchwartzBruhat g) (hm : IsSchwartzBruhat m) (c : ℂ) :
    D.twistedIntegral χ (g - c • m) = D.twistedIntegral χ g - c * D.twistedIntegral χ m := by
  unfold twistedIntegral
  have h : (fun x => (g - c • m) x * χ x) = (fun x => g x * χ x) + (-c) • fun x => m x * χ x := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hA := D.integrable_of_isSchwartzBruhat (isSchwartzBruhat_mul_char χ hg hχ)
  have hM := isSchwartzBruhat_mul_char χ hm hχ
  have hcM : D.Integrable ((-c) • fun x => m x * χ x) :=
    D.integrable_of_isSchwartzBruhat
      ((mem_sbSubmodule).mp ((sbSubmodule H).smul_mem (-c) ((mem_sbSubmodule).mpr hM)))
  rw [h, D.haarIntegral_add hA hcM, D.haarIntegral_smul (-c) (D.integrable_of_isSchwartzBruhat hM)]
  ring

private
theorem mem_of_twistedIntegral_eq_zero (hc : IsCompact (D.ref : Set H)) (hχ : IsLocallyConstant (fun x : H => χ x))
    {M : Submodule ℂ (H → ℂ)} (hle : twistedSpan χ ≤ M) {g : H → ℂ} (hg : IsSchwartzBruhat g)
    (h0 : D.twistedIntegral χ g = 0) : g ∈ M :=
  hle (D.mem_twistedSpan_of_twistedIntegral_eq_zero χ hc hχ hg h0)

private theorem mem_of_exists_twistedIntegral_ne_zero (hc : IsCompact (D.ref : Set H))
    (hχ : IsLocallyConstant (fun x : H => χ x)) {M : Submodule ℂ (H → ℂ)} (hle : twistedSpan χ ≤ M) {m : H → ℂ}
    (hmM : m ∈ M) (hm : IsSchwartzBruhat m) (hm0 : D.twistedIntegral χ m ≠ 0) {g : H → ℂ}
    (hg : IsSchwartzBruhat g) : g ∈ M := by
  set c : ℂ := D.twistedIntegral χ g / D.twistedIntegral χ m with hc_def
  have hsub : IsSchwartzBruhat (g - c • m) :=
    (mem_sbSubmodule).mp ((sbSubmodule H).sub_mem ((mem_sbSubmodule).mpr hg)
      ((sbSubmodule H).smul_mem c ((mem_sbSubmodule).mpr hm)))
  have h0 : D.twistedIntegral χ (g - c • m) = 0 := by
    rw [D.twistedIntegral_sub_smul χ hχ hg hm c, hc_def]
    rw [div_mul_cancel₀ _ hm0, sub_self]
  have h1 : g - c • m ∈ M := D.mem_of_twistedIntegral_eq_zero χ hc hχ hle hsub h0
  rw [← sub_add_cancel g (c • m)]
  exact M.add_mem h1 (M.smul_mem c hmM)

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section Field

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] (ψ : AddChar F ℂ)

private theorem isLocallyConstant_of_forall_mem_eq_one (U : AddSubgroup F) (hU : IsOpen (U : Set F))
    (h : ∀ s ∈ U, ψ s = 1) : IsLocallyConstant (fun x : F => ψ x) := by
  refine (IsLocallyConstant.iff_exists_open (fun x : F => ψ x)).mpr (fun x => ?_)
  refine ⟨(fun y : F => y - x) ⁻¹' (U : Set F), hU.preimage (continuous_id.sub continuous_const), ?_, ?_⟩
  · show x - x ∈ U
    rw [sub_self]
    exact U.zero_mem
  · intro x' hx'
    have hx'U : x' - x ∈ U := hx'
    have e : x + (x' - x) = x' := by abel
    show ψ x' = ψ x
    rw [← e, AddChar.map_add_eq_mul, h _ hx'U, mul_one]

private theorem exists_mem_ne_one_of_not_isLocallyConstant (hψ : ¬ IsLocallyConstant (fun x : F => ψ x))
    (U : AddSubgroup F) (hU : IsOpen (U : Set F)) : ∃ s ∈ U, ψ s ≠ 1 := by
  by_contra hcon
  exact hψ (isLocallyConstant_of_forall_mem_eq_one ψ U hU
    (fun s hs => Classical.byContradiction (fun hne => hcon ⟨s, hs, hne⟩)))

end Field
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {F K : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [AddCommGroup K]
  [TopologicalSpace K] [IsTopologicalAddGroup K] (ψ : AddChar F ℂ)

private theorem mem_of_not_isLocallyConstant (D : BallData K) (hψ : ¬ IsLocallyConstant (fun x : F => ψ x))
    (ι : F →+ K) (hι : Continuous ι) {M : Submodule ℂ (K → ℂ)}
    (hM : ∀ g : K → ℂ, IsSchwartzBruhat g → ∀ s : F, ψ s • (fun x => g (x + ι s)) - g ∈ M) {g : K → ℂ}
    (hg : IsSchwartzBruhat g) : g ∈ M := by
  obtain ⟨B, hB, hgB⟩ := D.exists_isBall_isInvariantUnder_of_isSchwartzBruhat hg
  have hU : IsOpen ((B.comap ι : AddSubgroup F) : Set F) := by
    exact (D.isOpen_of_isBall hB).preimage hι
  obtain ⟨s, hs, hne⟩ := exists_mem_ne_one_of_not_isLocallyConstant ψ hψ (B.comap ι) hU
  have hsB : ι s ∈ B := hs
  have hinv : (fun x => g (x + ι s)) = g := funext (fun x => hgB (ι s) hsB x)
  have hrel : (ψ s - 1) • g ∈ M := by
    have h1 := hM g hg s
    rw [hinv] at h1
    have e : (ψ s - 1) • g = ψ s • g - g := by rw [sub_smul, one_smul]
    rw [e]
    exact h1
  have hc : (ψ s - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hne
  have h2 := M.smul_mem (ψ s - 1)⁻¹ hrel
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

noncomputable section

open Function Set Topology

namespace SchwartzBruhatIntegral

private def HasClopenBasis (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U

section Nonarchimedean

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [NonarchimedeanAddGroup H]

private theorem hasClopenBasis_of_nonarchimedean : HasClopenBasis H := by
  intro y U hU hy
  have hW : IsOpen ((fun x : H => x + y) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have h0 : (0 : H) ∈ (fun x : H => x + y) ⁻¹' U := by
    show (0 : H) + y ∈ U
    rw [zero_add]
    exact hy
  obtain ⟨B, hBo, hBW⟩ : ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ (fun x : H => x + y) ⁻¹' U := by
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (hW.mem_nhds h0)
    exact ⟨V.toAddSubgroup, V.isOpen, hV⟩
  have hBc : IsClosed (B : Set H) := AddSubgroup.isClosed_of_isOpen B hBo
  refine ⟨(fun z : H => z - y) ⁻¹' (B : Set H),
    IsClopen.preimage (s := (B : Set H)) ⟨hBc, hBo⟩ (continuous_id.sub continuous_const), ?_, ?_⟩
  · show y - y ∈ B
    rw [sub_self]
    exact B.zero_mem
  · intro z hz
    have hz' : z - y ∈ B := hz
    have := hBW hz'
    show z ∈ U
    rwa [Set.mem_preimage, sub_add_cancel] at this

end Nonarchimedean
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Constructions

private theorem HasClopenBasis.of_isInducing {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] {f : Z → Y}
    (hf : IsInducing f) (hY : HasClopenBasis Y) : HasClopenBasis Z := by
  intro z U hU hz
  obtain ⟨O, hO, rfl⟩ := hf.isOpen_iff.mp hU
  obtain ⟨V, hV, hfV, hVO⟩ := hY (f z) O hO hz
  exact ⟨f ⁻¹' V, hV.preimage hf.continuous, hfV, fun w hw => hVO hw⟩

private
theorem HasClopenBasis.prod {Y₁ Y₂ : Type*} [TopologicalSpace Y₁] [TopologicalSpace Y₂] (h₁ : HasClopenBasis Y₁)
    (h₂ : HasClopenBasis Y₂) : HasClopenBasis (Y₁ × Y₂) := by
  rintro ⟨y₁, y₂⟩ U hU hy
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hy)
  obtain ⟨O₁, hO₁U, hO₁, hyO₁⟩ := mem_nhds_iff.mp hU₁
  obtain ⟨O₂, hO₂U, hO₂, hyO₂⟩ := mem_nhds_iff.mp hU₂
  obtain ⟨V₁, hV₁, hy₁, hV₁O⟩ := h₁ y₁ O₁ hO₁ hyO₁
  obtain ⟨V₂, hV₂, hy₂, hV₂O⟩ := h₂ y₂ O₂ hO₂ hyO₂
  refine ⟨V₁ ×ˢ V₂, hV₁.prod hV₂, ⟨hy₁, hy₂⟩, ?_⟩
  exact (Set.prod_mono (hV₁O.trans hO₁U) (hV₂O.trans hO₂U)).trans hsub

private theorem HasClopenBasis.units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    (h : HasClopenBasis G₀) : HasClopenBasis G₀ˣ :=
  HasClopenBasis.of_isInducing Units.isEmbedding_val₀.toIsInducing h

private
theorem HasClopenBasis.exists_isClopen_isCompact_mem {Y : Type*} [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y]
    (hY : HasClopenBasis Y) (t : Y) : ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ t ∈ V := by
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds t
  have ht : t ∈ interior K := mem_interior_iff_mem_nhds.mpr hKn
  obtain ⟨V, hV, htV, hVK⟩ := hY t (interior K) isOpen_interior ht
  exact ⟨V, hV, hKc.of_isClosed_subset hV.isClosed (hVK.trans interior_subset), htV⟩

end Constructions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

section

noncomputable section

open Function Set

namespace SchwartzBruhatIntegral

section Index

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

private theorem relIndex_ne_zero_of_isOpen_of_isCompact {B R : AddSubgroup H} (hB : IsOpen (B : Set H))
    (hR : IsCompact (R : Set H)) : B.relIndex R ≠ 0 := by
  haveI : CompactSpace R := isCompact_iff_compactSpace.mp hR
  have hopen : IsOpen ((B.addSubgroupOf R : AddSubgroup R) : Set R) := by
    rw [AddSubgroup.coe_addSubgroupOf]
    exact hB.preimage continuous_subtype_val
  haveI : DiscreteTopology (R ⧸ B.addSubgroupOf R) := QuotientAddGroup.discreteTopology hopen
  haveI : CompactSpace (R ⧸ B.addSubgroupOf R) := by
    first
    | infer_instance
    | exact ⟨by
        rw [← Set.image_univ_of_surjective (QuotientAddGroup.mk_surjective (s := B.addSubgroupOf R))]
        exact isCompact_univ.image (continuous_quotient_mk_addSubgroup (B.addSubgroupOf R))⟩
  haveI : Finite (R ⧸ B.addSubgroupOf R) := finite_of_compact_of_discrete
  exact AddSubgroup.index_ne_zero_of_finite

end Index
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

namespace BallData

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

private def ofCompactOpen (R : AddSubgroup H) (hRo : IsOpen (R : Set H)) (hRc : IsCompact (R : Set H))
    (hbasis : ∀ U ∈ nhds (0 : H), ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U) : BallData H where
  ref := R
  IsBall B := IsOpen (B : Set H) ∧ B ≤ R
  isBall_ref := ⟨hRo, le_rfl⟩
  le_ref h := h.2
  isOpen_of_isBall h := h.1
  relIndex_ne_zero h := relIndex_ne_zero_of_isOpen_of_isCompact h.1 hRc
  exists_isBall_le {B B'} h h' := by
    refine ⟨B ⊓ B', ⟨?_, inf_le_left.trans h.2⟩, inf_le_left, inf_le_right⟩
    rw [AddSubgroup.coe_inf]
    exact h.1.inter h'.1
  exists_isBall_subset U hU := by
    obtain ⟨B, hBo, hBU⟩ := hbasis U hU
    refine ⟨B ⊓ R, ⟨?_, inf_le_right⟩, ?_⟩
    · rw [AddSubgroup.coe_inf]
      exact hBo.inter hRo
    · rw [AddSubgroup.coe_inf]
      exact Set.inter_subset_left.trans hBU

private theorem ofCompactOpen_ref (R : AddSubgroup H) (hRo : IsOpen (R : Set H)) (hRc : IsCompact (R : Set H))
    (hbasis : ∀ U ∈ nhds (0 : H), ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U) :
    (ofCompactOpen R hRo hRc hbasis).ref = R :=
  rfl

private theorem ofCompactOpen_isBall_iff (R : AddSubgroup H) (hRo : IsOpen (R : Set H)) (hRc : IsCompact (R : Set H))
    (hbasis : ∀ U ∈ nhds (0 : H), ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U) (B : AddSubgroup H) :
    (ofCompactOpen R hRo hRc hbasis).IsBall B ↔ IsOpen (B : Set H) ∧ B ≤ R :=
  Iff.rfl

private
theorem isCompact_ref_ofCompactOpen (R : AddSubgroup H) (hRo : IsOpen (R : Set H)) (hRc : IsCompact (R : Set H))
    (hbasis : ∀ U ∈ nhds (0 : H), ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U) :
    IsCompact (((ofCompactOpen R hRo hRc hbasis).ref : AddSubgroup H) : Set H) :=
  hRc

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Prod

variable {H₁ H₂ : Type*} [AddCommGroup H₁] [TopologicalSpace H₁] [IsTopologicalAddGroup H₁]
  [AddCommGroup H₂] [TopologicalSpace H₂] [IsTopologicalAddGroup H₂]

private theorem isOpen_prod_addSubgroup {B₁ : AddSubgroup H₁} {B₂ : AddSubgroup H₂} (h₁ : IsOpen (B₁ : Set H₁))
    (h₂ : IsOpen (B₂ : Set H₂)) : IsOpen ((B₁.prod B₂ : AddSubgroup (H₁ × H₂)) : Set (H₁ × H₂)) := by
  rw [AddSubgroup.coe_prod]
  exact h₁.prod h₂

private theorem isCompact_prod_addSubgroup {B₁ : AddSubgroup H₁} {B₂ : AddSubgroup H₂} (h₁ : IsCompact (B₁ : Set H₁))
    (h₂ : IsCompact (B₂ : Set H₂)) : IsCompact ((B₁.prod B₂ : AddSubgroup (H₁ × H₂)) : Set (H₁ × H₂)) := by
  rw [AddSubgroup.coe_prod]
  exact h₁.prod h₂

private theorem exists_isOpen_addSubgroup_prod_subset (D₁ : BallData H₁) (D₂ : BallData H₂) (U : Set (H₁ × H₂))
    (hU : U ∈ nhds (0 : H₁ × H₂)) :
    ∃ B : AddSubgroup (H₁ × H₂), IsOpen (B : Set (H₁ × H₂)) ∧ (B : Set (H₁ × H₂)) ⊆ U := by
  have hU' : U ∈ nhds ((0 : H₁), (0 : H₂)) := hU
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.mp hU'
  obtain ⟨B₁, hB₁, hB₁U⟩ := D₁.exists_isBall_subset U₁ hU₁
  obtain ⟨B₂, hB₂, hB₂U⟩ := D₂.exists_isBall_subset U₂ hU₂
  refine ⟨B₁.prod B₂, isOpen_prod_addSubgroup (D₁.isOpen_of_isBall hB₁) (D₂.isOpen_of_isBall hB₂), ?_⟩
  rw [AddSubgroup.coe_prod]
  exact (Set.prod_mono hB₁U hB₂U).trans hsub

private def BallData.prod (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) : BallData (H₁ × H₂) :=
  BallData.ofCompactOpen (D₁.ref.prod D₂.ref)
    (isOpen_prod_addSubgroup (D₁.isOpen_of_isBall D₁.isBall_ref) (D₂.isOpen_of_isBall D₂.isBall_ref))
    (isCompact_prod_addSubgroup hc₁ hc₂) (exists_isOpen_addSubgroup_prod_subset D₁ D₂)

private theorem BallData.prod_ref (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) : (D₁.prod hc₁ D₂ hc₂).ref = D₁.ref.prod D₂.ref :=
  rfl

private theorem BallData.isCompact_ref_prod (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) :
    IsCompact (((D₁.prod hc₁ D₂ hc₂).ref : AddSubgroup (H₁ × H₂)) : Set (H₁ × H₂)) :=
  isCompact_prod_addSubgroup hc₁ hc₂

private theorem BallData.isBall_prod (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) {B₁ : AddSubgroup H₁} {B₂ : AddSubgroup H₂} (h₁ : D₁.IsBall B₁)
    (h₂ : D₂.IsBall B₂) : (D₁.prod hc₁ D₂ hc₂).IsBall (B₁.prod B₂) :=
  ⟨isOpen_prod_addSubgroup (D₁.isOpen_of_isBall h₁) (D₂.isOpen_of_isBall h₂),
    AddSubgroup.prod_mono (D₁.le_ref h₁) (D₂.le_ref h₂)⟩

end Prod
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open Function Set

namespace SchwartzBruhatIntegral

section Nonarchimedean

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [NonarchimedeanAddGroup H]

private theorem exists_isOpen_addSubgroup_subset (U : Set H) (hU : U ∈ nhds (0 : H)) :
    ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U := by
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  exact ⟨V.toAddSubgroup, V.isOpen, hV⟩

private def BallData.ofNonarchimedean (R : AddSubgroup H) (hRo : IsOpen (R : Set H)) (hRc : IsCompact (R : Set H)) :
    BallData H :=
  BallData.ofCompactOpen R hRo hRc exists_isOpen_addSubgroup_subset

private theorem BallData.ofNonarchimedean_ref (R : AddSubgroup H) (hRo : IsOpen (R : Set H))
    (hRc : IsCompact (R : Set H)) : (BallData.ofNonarchimedean R hRo hRc).ref = R :=
  rfl

private theorem BallData.isCompact_ref_ofNonarchimedean (R : AddSubgroup H) (hRo : IsOpen (R : Set H))
    (hRc : IsCompact (R : Set H)) : IsCompact (((BallData.ofNonarchimedean R hRo hRc).ref : AddSubgroup H) : Set H) :=
  hRc

end Nonarchimedean
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Admissible

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

private theorem BallData.isAdmissibleAut_ofCompactOpen (R : AddSubgroup H) (hRo : IsOpen (R : Set H))
    (hRc : IsCompact (R : Set H))
    (hbasis : ∀ U ∈ nhds (0 : H), ∃ B : AddSubgroup H, IsOpen (B : Set H) ∧ (B : Set H) ⊆ U) (e : H ≃+ H)
    (he : Continuous e) (he' : Continuous e.symm) (href : ∀ x, e x ∈ R ↔ x ∈ R) :
    (BallData.ofCompactOpen R hRo hRc hbasis).IsAdmissibleAut e where
  continuous_toFun := he
  continuous_invFun := he'
  map_ref := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (href x).mpr hx
    · intro hy
      refine ⟨e.symm y, (href (e.symm y)).mp ?_, e.apply_symm_apply y⟩
      rwa [AddEquiv.apply_symm_apply]
  isBall_comap := by
    intro B hB
    refine ⟨?_, fun x hx => ?_⟩
    · rw [AddSubgroup.coe_comap]
      exact hB.1.preimage he
    · exact (href x).mp (hB.2 hx)

end Admissible
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section LocalField

open IsDedekindDomain NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def integerSubgroup : AddSubgroup (v.adicCompletion ℚ) :=
  (v.adicCompletionIntegers ℚ).toSubring.toAddSubgroup

private
theorem mem_integerSubgroup_iff (x : v.adicCompletion ℚ) : x ∈ integerSubgroup v ↔ x ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

private theorem isOpen_integerSubgroup :
    IsOpen ((integerSubgroup v : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) := by
  have h : IsOpen ((v.adicCompletionIntegers ℚ : ValuationSubring (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) :=
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v
  exact h

private theorem isCompact_integerSubgroup :
    IsCompact ((integerSubgroup v : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) := by
  haveI : CompactSpace (v.adicCompletionIntegers ℚ) := AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 ℚ) ℚ v
  have h :
      IsCompact ((v.adicCompletionIntegers ℚ : ValuationSubring (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr this
  exact h

private def localBallData : BallData (v.adicCompletion ℚ) :=
  BallData.ofNonarchimedean (integerSubgroup v) (isOpen_integerSubgroup v) (isCompact_integerSubgroup v)

private theorem localBallData_ref : (localBallData v).ref = integerSubgroup v :=
  rfl

private theorem isCompact_ref_localBallData :
    IsCompact (((localBallData v).ref : AddSubgroup (v.adicCompletion ℚ)) : Set (v.adicCompletion ℚ)) :=
  isCompact_integerSubgroup v

private theorem localBallData_isBall_iff (B : AddSubgroup (v.adicCompletion ℚ)) :
    (localBallData v).IsBall B ↔ IsOpen (B : Set (v.adicCompletion ℚ)) ∧ B ≤ integerSubgroup v :=
  Iff.rfl

end LocalField
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

namespace SchwartzBruhatIntegral

namespace BallData

variable {H₁ H₂ : Type*} [AddCommGroup H₁] [TopologicalSpace H₁] [IsTopologicalAddGroup H₁] [AddCommGroup H₂]
  [TopologicalSpace H₂] [IsTopologicalAddGroup H₂]

private theorem isAdmissibleAut_prod (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) (e : H₁ × H₂ ≃+ H₁ × H₂) (he : Continuous e) (he' : Continuous e.symm)
    (href : ∀ x : H₁ × H₂, e x ∈ D₁.ref.prod D₂.ref ↔ x ∈ D₁.ref.prod D₂.ref) :
    (D₁.prod hc₁ D₂ hc₂).IsAdmissibleAut e :=
  BallData.isAdmissibleAut_ofCompactOpen _ _ _ _ e he he' href

private
theorem isAdmissibleAut_prod_of_forall (D₁ : BallData H₁) (hc₁ : IsCompact (D₁.ref : Set H₁)) (D₂ : BallData H₂)
    (hc₂ : IsCompact (D₂.ref : Set H₂)) (e : H₁ × H₂ ≃+ H₁ × H₂) (he : Continuous e) (he' : Continuous e.symm)
    (href : ∀ x : H₁ × H₂, ((e x).1 ∈ D₁.ref ∧ (e x).2 ∈ D₂.ref) ↔ (x.1 ∈ D₁.ref ∧ x.2 ∈ D₂.ref)) :
    (D₁.prod hc₁ D₂ hc₂).IsAdmissibleAut e := by
  refine isAdmissibleAut_prod D₁ hc₁ D₂ hc₂ e he he' (fun x => ?_)
  rw [AddSubgroup.mem_prod, AddSubgroup.mem_prod]
  exact href x

end BallData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

open IsDedekindDomain

namespace SchwartzBruhatIntegral

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private theorem hasClopenBasis_localField : HasClopenBasis (v.adicCompletion ℚ) :=
  hasClopenBasis_of_nonarchimedean

private theorem hasClopenBasis_units_localField : HasClopenBasis (v.adicCompletion ℚ)ˣ :=
  (hasClopenBasis_localField v).units

private theorem hasClopenBasis_torus :
    HasClopenBasis ((v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ) :=
  (hasClopenBasis_units_localField v).prod
    ((hasClopenBasis_units_localField v).prod (hasClopenBasis_units_localField v))

private theorem exists_isClopen_isCompact_mem_torus
    (t : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ) :
    ∃ V : Set ((v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ),
      IsClopen V ∧ IsCompact V ∧ t ∈ V :=
  (hasClopenBasis_torus v).exists_isClopen_isCompact_mem t

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

noncomputable section

namespace SchwartzBruhatIntegral

variable {G : Type*} [TopologicalSpace G] {U C : Set G} {Z : Set U}

private def nestedSetHomeo (hCU : C ⊆ U) (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C) : Z ≃ₜ C where
  toFun x := ⟨(x.1 : G), (hZ x.1).mp x.2⟩
  invFun g := ⟨⟨g.1, hCU g.2⟩, (hZ ⟨g.1, hCU g.2⟩).mpr g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem coe_nestedSetHomeo_apply (hCU : C ⊆ U) (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C) (x : Z) :
    ((nestedSetHomeo hCU hZ x : C) : G) = ((x : U) : G) :=
  rfl

private theorem coe_coe_nestedSetHomeo_symm_apply (hCU : C ⊆ U) (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C) (g : C) :
    (((nestedSetHomeo hCU hZ).symm g : U) : G) = (g : G) :=
  rfl

private def nestedChart {M : Type*} [TopologicalSpace M] (hCU : C ⊆ U) (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C)
    (e : C ≃ₜ M) : Z ≃ₜ M :=
  (nestedSetHomeo hCU hZ).trans e

private theorem nestedChart_apply {M : Type*} [TopologicalSpace M] (hCU : C ⊆ U) (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C)
    (e : C ≃ₜ M) (x : Z) : nestedChart hCU hZ e x = e (nestedSetHomeo hCU hZ x) :=
  rfl

private theorem coe_coe_nestedChart_symm_apply {M : Type*} [TopologicalSpace M] (hCU : C ⊆ U)
    (hZ : ∀ x : U, x ∈ Z ↔ (x : G) ∈ C) (e : C ≃ₜ M) (m : M) :
    (((nestedChart hCU hZ e).symm m : U) : G) = ((e.symm m : C) : G) :=
  rfl

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

namespace SchwartzBruhatIntegral

variable {F K : Type*} [AddMonoid F] [TopologicalSpace F] [TopologicalSpace K]

private theorem isLocallyConstant_of_coe_eq [AddMonoid K] {ψ : AddChar K ℂ} {f : K → ℂ} (hf : IsLocallyConstant f)
    (h : ∀ k, ψ k = f k) : IsLocallyConstant (fun k : K => ψ k) := by
  have h' : (fun k : K => ψ k) = f := funext h
  rw [h']
  exact hf

variable (χ : AddChar F ℂ) (hχ : IsLocallyConstant (fun x : F => χ x))

include hχ

private
theorem isLocallyConstant_char_comp {π : K → F} (hπ : Continuous π) : IsLocallyConstant (fun k : K => χ (π k)) :=
  hχ.comp_continuous hπ

private theorem isLocallyConstant_char_comp_two {π₁ π₂ : K → F} (h₁ : Continuous π₁) (h₂ : Continuous π₂) :
    IsLocallyConstant (fun k : K => χ (π₁ k) * χ (π₂ k)) :=
  (hχ.comp_continuous h₁).mul (hχ.comp_continuous h₂)

private theorem isLocallyConstant_char_comp_three {π₁ π₂ π₃ : K → F} (h₁ : Continuous π₁) (h₂ : Continuous π₂)
    (h₃ : Continuous π₃) : IsLocallyConstant (fun k : K => χ (π₁ k) * χ (π₂ k) * χ (π₃ k)) :=
  ((hχ.comp_continuous h₁).mul (hχ.comp_continuous h₂)).mul (hχ.comp_continuous h₃)

private theorem isLocallyConstant_char_comp_four {π₁ π₂ π₃ π₄ : K → F} (h₁ : Continuous π₁) (h₂ : Continuous π₂)
    (h₃ : Continuous π₃) (h₄ : Continuous π₄) :
    IsLocallyConstant (fun k : K => χ (π₁ k) * χ (π₂ k) * χ (π₃ k) * χ (π₄ k)) :=
  (((hχ.comp_continuous h₁).mul (hχ.comp_continuous h₂)).mul (hχ.comp_continuous h₃)).mul
    (hχ.comp_continuous h₄)

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatSpace SchwartzBruhatIntegral Function

namespace WhittakerCoinvariantsGL3

namespace Descent

section Factor

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] {Z : Set X}

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem apply_eq_zero_of_restrictClosed_eq_zero (hZ : IsClosed Z) (D : testSpace X →ₗ[ℂ] ℂ)
    (hD : ∀ ψ : testSpace ↥Zᶜ, D (extendByZero hZ.isOpen_compl ψ) = 0) {φ : testSpace X}
    (hφ : restrictClosed hZ φ = 0) : D φ = 0 := by
  have hk : φ ∈ LinearMap.ker (restrictClosed hZ) := LinearMap.mem_ker.mpr hφ
  rw [ker_restrictClosed hZ] at hk
  obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hk
  rw [← hψ]
  exact hD ψ

private def lift (hZ : IsClosed Z) (h : testSpace Z) : testSpace X :=
  surjInv (restrictClosed_surjective hZ) h

private theorem restrictClosed_lift (hZ : IsClosed Z) (h : testSpace Z) :
    restrictClosed hZ (lift hZ h) = h :=
  surjInv_eq (restrictClosed_surjective hZ) h

private def factor (hZ : IsClosed Z) (D : testSpace X →ₗ[ℂ] ℂ)
    (hD : ∀ ψ : testSpace ↥Zᶜ, D (extendByZero hZ.isOpen_compl ψ) = 0) : testSpace Z →ₗ[ℂ] ℂ where
  toFun h := D (lift hZ h)
  map_add' h₁ h₂ := by
    have h := apply_eq_zero_of_restrictClosed_eq_zero hZ D hD
      (φ := lift hZ (h₁ + h₂) - (lift hZ h₁ + lift hZ h₂))
      (by rw [map_sub, map_add, restrictClosed_lift, restrictClosed_lift, restrictClosed_lift,
        sub_self])
    rw [map_sub, map_add, sub_eq_zero] at h
    exact h
  map_smul' c h := by
    have h' := apply_eq_zero_of_restrictClosed_eq_zero hZ D hD
      (φ := lift hZ (c • h) - c • lift hZ h)
      (by rw [map_sub, map_smul, restrictClosed_lift, restrictClosed_lift, sub_self])
    rw [map_sub, map_smul, sub_eq_zero] at h'
    rw [RingHom.id_apply]
    exact h'

private theorem factor_apply_restrictClosed (hZ : IsClosed Z) (D : testSpace X →ₗ[ℂ] ℂ)
    (hD : ∀ ψ : testSpace ↥Zᶜ, D (extendByZero hZ.isOpen_compl ψ) = 0) (φ : testSpace X) :
    factor hZ D hD (restrictClosed hZ φ) = D φ := by
  show D (lift hZ (restrictClosed hZ φ)) = D φ
  have h := apply_eq_zero_of_restrictClosed_eq_zero hZ D hD
    (φ := lift hZ (restrictClosed hZ φ) - φ)
    (by rw [map_sub, restrictClosed_lift, sub_self])
  rw [map_sub, sub_eq_zero] at h
  exact h

private theorem eq_zero_of_factor_eq_zero (hZ : IsClosed Z) (D : testSpace X →ₗ[ℂ] ℂ)
    (hD : ∀ ψ : testSpace ↥Zᶜ, D (extendByZero hZ.isOpen_compl ψ) = 0) (h0 : factor hZ D hD = 0)
    (φ : testSpace X) : D φ = 0 := by
  rw [← factor_apply_restrictClosed hZ D hD φ, h0, LinearMap.zero_apply]

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in

private theorem restrictClosed_smul_comapHomeomorph (hZ : IsClosed Z) (R : X ≃ₜ X)
    (hR : ∀ x, x ∈ Z ↔ R x ∈ Z) (c : ℂ) (φ : testSpace X) :
    restrictClosed hZ (c • comapHomeomorph R φ) =
      c • comapHomeomorph (R.subtype hR) (restrictClosed hZ φ) := by
  apply Subtype.ext
  funext z
  rfl

private theorem factor_smul_comapHomeomorph (hZ : IsClosed Z) (D : testSpace X →ₗ[ℂ] ℂ)
    (hD : ∀ ψ : testSpace ↥Zᶜ, D (extendByZero hZ.isOpen_compl ψ) = 0) (R : X ≃ₜ X)
    (hR : ∀ x, x ∈ Z ↔ R x ∈ Z) (c d : ℂ)
    (hDR : ∀ φ : testSpace X, D (c • comapHomeomorph R φ) = d • D φ) (h : testSpace Z) :
    factor hZ D hD (c • comapHomeomorph (R.subtype hR) h) = d • factor hZ D hD h := by
  obtain ⟨φ, rfl⟩ := restrictClosed_surjective hZ h
  rw [← restrictClosed_smul_comapHomeomorph hZ R hR c φ, factor_apply_restrictClosed,
    factor_apply_restrictClosed, hDR]

end Factor
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Extend

variable {X : Type*} [TopologicalSpace X] [T2Space X] {U : Set X}

private theorem extendByZero_smul_comapHomeomorph (hU : IsOpen U) (R : X ≃ₜ X)
    (hR : ∀ x, x ∈ U ↔ R x ∈ U) (c : ℂ) (φ : testSpace U) :
    extendByZero hU (c • comapHomeomorph (R.subtype hR) φ) =
      c • comapHomeomorph R (extendByZero hU φ) := by
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ U
  · have e₁ := extendByZero_apply_coe hU (c • comapHomeomorph (R.subtype hR) φ) ⟨x, hx⟩
    have e₂ := extendByZero_apply_coe hU φ ⟨R x, (hR x).mp hx⟩
    exact e₁.trans (congrArg (c * ·) e₂.symm)
  · have e₁ := extendByZero_apply_of_notMem hU (c • comapHomeomorph (R.subtype hR) φ) hx
    have e₂ := extendByZero_apply_of_notMem hU φ (fun h => hx ((hR x).mpr h))
    exact e₁.trans ((mul_zero c).symm.trans (congrArg (c * ·) e₂.symm))

private theorem comp_extendByZero_smul_comapHomeomorph (hU : IsOpen U) (D : testSpace X →ₗ[ℂ] ℂ)
    (R : X ≃ₜ X) (hR : ∀ x, x ∈ U ↔ R x ∈ U) (c d : ℂ)
    (hDR : ∀ φ : testSpace X, D (c • comapHomeomorph R φ) = d • D φ) (φ : testSpace U) :
    (D ∘ₗ extendByZero hU) (c • comapHomeomorph (R.subtype hR) φ) =
      d • (D ∘ₗ extendByZero hU) φ := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, extendByZero_smul_comapHomeomorph, hDR]

end Extend
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Piece

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

private def VanishesOn (D : testSpace X →ₗ[ℂ] ℂ) (U : Set X) : Prop :=
  ∀ φ : testSpace X, (∀ x, x ∉ U → (φ : X → ℂ) x = 0) → D φ = 0

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem vanishesOn_empty (D : testSpace X →ₗ[ℂ] ℂ) : VanishesOn D ∅ := by
  intro φ hφ
  have h0 : φ = 0 := by
    apply Subtype.ext
    funext x
    exact hφ x (Set.notMem_empty x)
  rw [h0, map_zero]

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem apply_eq_zero_of_vanishesOn_univ (D : testSpace X →ₗ[ℂ] ℂ) (h : VanishesOn D Set.univ)
    (φ : testSpace X) : D φ = 0 :=
  h φ (fun x hx => absurd (Set.mem_univ x) hx)

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem VanishesOn.mono {D : testSpace X →ₗ[ℂ] ℂ} {U V : Set X} (h : VanishesOn D V) (hUV : U ⊆ V) :
    VanishesOn D U :=
  fun φ hφ => h φ (fun x hx => hφ x (fun hxU => hx (hUV hxU)))

variable {U C : Set X}

private def pieceIn (U C : Set X) : Set U :=
  Subtype.val ⁻¹' C

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem mem_pieceIn {x : U} : x ∈ pieceIn U C ↔ (x : X) ∈ C :=
  Iff.rfl

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
private theorem vanishes_compl_pieceIn (hU : IsOpen U) (hC : IsClosed (pieceIn U C))
    (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C)) (ψ : testSpace ↥(pieceIn U C)ᶜ) :
    (D ∘ₗ extendByZero hU) (extendByZero hC.isOpen_compl ψ) = 0 := by
  rw [LinearMap.comp_apply]
  refine hD _ (fun x hx => ?_)
  by_cases hxU : x ∈ U
  · have hxC : x ∈ C := by
      by_contra hxC
      exact hx ⟨hxU, hxC⟩
    have e₁ := extendByZero_apply_coe hU (extendByZero hC.isOpen_compl ψ) ⟨x, hxU⟩
    have e₂ := extendByZero_apply_of_notMem hC.isOpen_compl ψ (x := (⟨x, hxU⟩ : U))
      (fun h => h hxC)
    exact e₁.trans e₂
  · exact extendByZero_apply_of_notMem hU _ hxU

private def pieceFunctional (hU : IsOpen U) (hCU : C ⊆ U) (hC : IsClosed (pieceIn U C))
    (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C)) : testSpace C →ₗ[ℂ] ℂ :=
  haveI := hU.locallyCompactSpace
  factor hC (D ∘ₗ extendByZero hU) (vanishes_compl_pieceIn hU hC D hD) ∘ₗ
    (comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl))).toLinearMap

private theorem pieceFunctional_apply (hU : IsOpen U) (hCU : C ⊆ U) (hC : IsClosed (pieceIn U C))
    (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C)) (h : testSpace C) :
    haveI := hU.locallyCompactSpace
    pieceFunctional hU hCU hC D hD h = factor hC (D ∘ₗ extendByZero hU)
      (vanishes_compl_pieceIn hU hC D hD)
      (comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl)) h) :=
  rfl

private theorem vanishesOn_of_pieceFunctional_eq_zero (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsClosed (pieceIn U C)) (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C))
    (h0 : pieceFunctional hU hCU hC D hD = 0) : VanishesOn D U := by
  haveI := hU.locallyCompactSpace
  intro φ hφ
  obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.mp ((mem_range_extendByZero_iff hU).mpr hφ)
  have hfac := factor_apply_restrictClosed hC (D ∘ₗ extendByZero hU)
    (vanishes_compl_pieceIn hU hC D hD) ψ
  rw [LinearMap.comp_apply] at hfac
  rw [← hfac]
  have key := LinearMap.congr_fun h0
    ((comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl))).symm
      (restrictClosed hC ψ))
  rw [LinearMap.zero_apply, pieceFunctional_apply, LinearEquiv.apply_symm_apply] at key
  exact key

private theorem pieceFunctional_smul_comapHomeomorph (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsClosed (pieceIn U C)) (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C))
    (R : X ≃ₜ X) (hRU : ∀ x, x ∈ U ↔ R x ∈ U) (hRC : ∀ x, x ∈ C ↔ R x ∈ C) (c d : ℂ)
    (hDR : ∀ φ : testSpace X, D (c • comapHomeomorph R φ) = d • D φ) (h : testSpace C) :
    pieceFunctional hU hCU hC D hD (c • comapHomeomorph (R.subtype hRC) h) =
      d • pieceFunctional hU hCU hC D hD h := by
  haveI := hU.locallyCompactSpace
  have hRZ : ∀ u : U, u ∈ pieceIn U C ↔ (R.subtype hRU) u ∈ pieceIn U C :=
    fun u => hRC (u : X)
  have hcomm : comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl))
        (c • comapHomeomorph (R.subtype hRC) h) =
      c • comapHomeomorph ((R.subtype hRU).subtype hRZ)
        (comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl)) h) := by
    apply Subtype.ext
    funext z
    rfl
  rw [pieceFunctional_apply, pieceFunctional_apply, hcomm]
  exact factor_smul_comapHomeomorph hC (D ∘ₗ extendByZero hU) (vanishes_compl_pieceIn hU hC D hD)
    (R.subtype hRU) hRZ c d (comp_extendByZero_smul_comapHomeomorph hU D R hRU c d hDR)
    (comapHomeomorph (nestedSetHomeo (Z := pieceIn U C) hCU (fun _ => Iff.rfl)) h)

private theorem vanishesOn_of_forall_eq_zero {ι : Type*} (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsClosed (pieceIn U C)) (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C))
    (R : ι → X ≃ₜ X) (hRU : ∀ i x, x ∈ U ↔ R i x ∈ U) (hRC : ∀ i x, x ∈ C ↔ R i x ∈ C)
    (c : ι → ℂ) (hDR : ∀ i, ∀ φ : testSpace X, D (c i • comapHomeomorph (R i) φ) = D φ)
    (Θ : X ≃ₜ X) (hΘU : ∀ x, x ∈ U ↔ Θ x ∈ U) (hΘC : ∀ x, x ∈ C ↔ Θ x ∈ C)
    (hDΘ : ∀ φ : testSpace X, D (comapHomeomorph Θ φ) = -D φ)
    (hkill : ∀ E : testSpace C →ₗ[ℂ] ℂ,
      (∀ i, ∀ h : testSpace C, E (c i • comapHomeomorph ((R i).subtype (hRC i)) h) = E h) →
      (∀ h : testSpace C, E (comapHomeomorph (Θ.subtype hΘC) h) = -E h) → E = 0) :
    VanishesOn D U := by
  refine vanishesOn_of_pieceFunctional_eq_zero hU hCU hC D hD (hkill _ ?_ ?_)
  · intro i h
    have := pieceFunctional_smul_comapHomeomorph hU hCU hC D hD (R i) (hRU i) (hRC i) (c i) 1
      (fun φ => by rw [hDR i φ, one_smul]) h
    rw [one_smul] at this
    exact this
  · intro h
    have := pieceFunctional_smul_comapHomeomorph hU hCU hC D hD Θ hΘU hΘC 1 (-1)
      (fun φ => by rw [one_smul, hDΘ φ, neg_one_smul]) h
    rw [one_smul, neg_one_smul] at this
    exact this

private theorem vanishesOn_of_forall_eq_zero' {ι : Type*} (hU : IsOpen U) (hCU : C ⊆ U)
    (hC : IsClosed (pieceIn U C)) (D : testSpace X →ₗ[ℂ] ℂ) (hD : VanishesOn D (U \ C))
    (R : ι → X ≃ₜ X) (hRU : ∀ i x, x ∈ U ↔ R i x ∈ U) (hRC : ∀ i x, x ∈ C ↔ R i x ∈ C)
    (c : ι → ℂ) (hDR : ∀ i, ∀ φ : testSpace X, D (c i • comapHomeomorph (R i) φ) = D φ)
    (hkill : ∀ E : testSpace C →ₗ[ℂ] ℂ,
      (∀ i, ∀ h : testSpace C, E (c i • comapHomeomorph ((R i).subtype (hRC i)) h) = E h) → E = 0) :
    VanishesOn D U := by
  refine vanishesOn_of_pieceFunctional_eq_zero hU hCU hC D hD (hkill _ ?_)
  intro i h
  have := pieceFunctional_smul_comapHomeomorph hU hCU hC D hD (R i) (hRU i) (hRC i) (c i) 1
    (fun φ => by rw [hDR i φ, one_smul]) h
  rw [one_smul] at this
  exact this

end Piece
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Transport

variable {Y M : Type*} [TopologicalSpace Y] [TopologicalSpace M]

private theorem eq_zero_of_forall_eq_neg {E : testSpace Y →ₗ[ℂ] ℂ} {Θ : Y ≃ₜ Y}
    (hsymm : ∀ h : testSpace Y, E (comapHomeomorph Θ h) = E h)
    (hanti : ∀ h : testSpace Y, E (comapHomeomorph Θ h) = -E h) : E = 0 := by
  refine LinearMap.ext fun h => ?_
  have h2 : (2 : ℂ) * E h = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← hsymm h]
    rw [hanti h, neg_add_cancel]
  rw [LinearMap.zero_apply]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private def transport (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) : testSpace M →ₗ[ℂ] ℂ :=
  E ∘ₗ (comapHomeomorph e).toLinearMap

private theorem transport_apply (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) (f : testSpace M) :
    transport E e f = E (comapHomeomorph e f) :=
  rfl

private theorem transport_smul_comapHomeomorph (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) (R : Y ≃ₜ Y)
    (S : M ≃ₜ M) (hS : ∀ y, e (R y) = S (e y)) (c d : ℂ)
    (hE : ∀ h : testSpace Y, E (c • comapHomeomorph R h) = d • E h) (f : testSpace M) :
    transport E e (c • comapHomeomorph S f) = d • transport E e f := by
  rw [transport_apply, transport_apply, ← hE]
  congr 1
  apply Subtype.ext
  funext y
  show c * (f : M → ℂ) (S (e y)) = c * (f : M → ℂ) (e (R y))
  rw [hS]

private theorem smul_comapHomeomorph_of_transport (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) (R : Y ≃ₜ Y)
    (S : M ≃ₜ M) (hS : ∀ y, e (R y) = S (e y)) (c d : ℂ)
    (hT : ∀ f : testSpace M, transport E e (c • comapHomeomorph S f) = d • transport E e f)
    (h : testSpace Y) : E (c • comapHomeomorph R h) = d • E h := by
  have key := hT ((comapHomeomorph e).symm h)
  rw [transport_apply, transport_apply, LinearEquiv.apply_symm_apply] at key
  rw [← key]
  congr 1
  apply Subtype.ext
  funext y
  show c * (h : Y → ℂ) (R y) = c * (h : Y → ℂ) (e.symm (S (e y)))
  rw [← hS, Homeomorph.symm_apply_apply]

private theorem exists_extension (T₀ : testSpace M →ₗ[ℂ] ℂ) :
    ∃ T : (M → ℂ) →ₗ[ℂ] ℂ, ∀ f : testSpace M, T (f : M → ℂ) = T₀ f := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  refine ⟨T, fun f => ?_⟩
  have := LinearMap.congr_fun hT f
  exact this

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end Descent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

namespace WhittakerCoinvariantsGL3

variable {F : Type*} [Field F]

section LeftRootGroups

private def leftRoot12 (s : F) : F × F × F → F × F × F := fun ⟨a, b, c⟩ => ⟨a + s, b, c + b * s⟩

private def leftRoot23 (s : F) : F × F × F → F × F × F := fun ⟨a, b, c⟩ => ⟨a, b + s, c⟩

private def leftRoot13 (s : F) : F × F × F → F × F × F := fun ⟨a, b, c⟩ => ⟨a, b, c + s⟩

private theorem leftRoot12_neg_comp (s : F) (x : F × F × F) : leftRoot12 (-s) (leftRoot12 s x) = x := by
  obtain ⟨a, b, c⟩ := x
  dsimp only [leftRoot12]
  ext <;> ring1

private theorem leftRoot23_neg_comp (s : F) (x : F × F × F) : leftRoot23 (-s) (leftRoot23 s x) = x := by
  obtain ⟨a, b, c⟩ := x
  dsimp only [leftRoot23]
  ext <;> ring1

private theorem leftRoot13_neg_comp (s : F) (x : F × F × F) : leftRoot13 (-s) (leftRoot13 s x) = x := by
  obtain ⟨a, b, c⟩ := x
  dsimp only [leftRoot13]
  ext <;> ring1

end LeftRootGroups
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section BigCell

private def bigCellRight12 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) :=
  fun ⟨n, t, ⟨p, q, r⟩⟩ => ⟨n, t, ⟨p + s, q, r⟩⟩

private def bigCellRight23 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) :=
  fun ⟨n, t, ⟨p, q, r⟩⟩ => ⟨n, t, ⟨p, q + s, r + p * s⟩⟩

private def bigCellRight13 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) :=
  fun ⟨n, t, ⟨p, q, r⟩⟩ => ⟨n, t, ⟨p, q, r + s⟩⟩

private def bigCellInvolution :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) :=
  fun ⟨⟨a, b, c⟩, t, ⟨p, q, r⟩⟩ => ⟨⟨q, p, r⟩, t, ⟨b, a, c⟩⟩

private theorem bigCellInvolution_involutive : Function.Involutive (bigCellInvolution (F := F)) := by
  rintro ⟨⟨a, b, c⟩, t, ⟨p, q, r⟩⟩
  rfl

private theorem bigCellInvolution_torus (n : F × F × F) (t : Fˣ × Fˣ × Fˣ) (u : F × F × F) :
    (bigCellInvolution (n, t, u)).2.1 = t := by
  obtain ⟨a, b, c⟩ := n
  obtain ⟨p, q, r⟩ := u
  rfl

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Cycle123

private def cycle123Right12 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ =>
    ⟨⟨a, b + s * ((t₂ * t₃⁻¹ : Fˣ) : F), c + a * s * ((t₂ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩,
      ⟨q, r - q * s⟩⟩

private def cycle123Right23 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨n, t, ⟨q, r⟩⟩ => ⟨n, t, ⟨q + s, r⟩⟩

private def cycle123Right13 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨n, t, ⟨q, r⟩⟩ => ⟨n, t, ⟨q, r + s⟩⟩

private def cycle123Involution :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ =>
    ⟨⟨q, b * ((t₃ * t₂⁻¹ : Fˣ) : F), b * q * ((t₃ * t₂⁻¹ : Fˣ) : F) + r⟩, ⟨t₁, t₃, t₂⟩,
      ⟨a, c - a * b⟩⟩

private theorem cycle123Involution_involutive :
    Function.Involutive (cycle123Involution (F := F)) := by
  rintro ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  have h₃ : (t₃ : F) ≠ 0 := t₃.ne_zero
  dsimp only [cycle123Involution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

private theorem cycle123Involution_torus (n : F × F × F) (t₁ t₂ t₃ : Fˣ) (u : F × F) :
    (cycle123Involution (n, (t₁, t₂, t₃), u)).2.1 = (t₁, t₃, t₂) := by
  obtain ⟨a, b, c⟩ := n
  obtain ⟨q, r⟩ := u
  rfl

private theorem cycle123Involution_of_eq (a b c q r : F) (t₁ t₂ t₃ : Fˣ) (h : t₂ = t₃) :
    cycle123Involution ((a, b, c), (t₁, t₂, t₃), (q, r)) =
      ((q, b, b * q + r), (t₁, t₂, t₃), (a, c - a * b)) := by
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  subst h
  dsimp only [cycle123Involution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

end Cycle123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Cycle132

private def cycle132Right12 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨n, t, ⟨p, r⟩⟩ => ⟨n, t, ⟨p + s, r⟩⟩

private def cycle132Right23 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ =>
    ⟨⟨a + s * ((t₁ * t₂⁻¹ : Fˣ) : F), b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r + p * s⟩⟩

private def cycle132Right13 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨n, t, ⟨p, r⟩⟩ => ⟨n, t, ⟨p, r + s⟩⟩

private def cycle132Involution :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ =>
    ⟨⟨a * ((t₂ * t₁⁻¹ : Fˣ) : F), p, r⟩, ⟨t₂, t₁, t₃⟩, ⟨b, c⟩⟩

private theorem cycle132Involution_involutive :
    Function.Involutive (cycle132Involution (F := F)) := by
  rintro ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩
  have h₁ : (t₁ : F) ≠ 0 := t₁.ne_zero
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  dsimp only [cycle132Involution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

private theorem cycle132Involution_torus (n : F × F × F) (t₁ t₂ t₃ : Fˣ) (u : F × F) :
    (cycle132Involution (n, (t₁, t₂, t₃), u)).2.1 = (t₂, t₁, t₃) := by
  obtain ⟨a, b, c⟩ := n
  obtain ⟨p, r⟩ := u
  rfl

private theorem cycle132Involution_of_eq (a b c p r : F) (t₁ t₂ t₃ : Fˣ) (h : t₁ = t₂) :
    cycle132Involution ((a, b, c), (t₁, t₂, t₃), (p, r)) =
      ((a, p, r), (t₁, t₂, t₃), (b, c)) := by
  have h₁ : (t₁ : F) ≠ 0 := t₁.ne_zero
  subst h
  dsimp only [cycle132Involution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

end Cycle132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section ReflectionCells

private def refl12Right12 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨n, t, p⟩ => ⟨n, t, p + s⟩

private def refl12Right23 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ =>
    ⟨⟨a, b + p * s * ((t₂ * t₃⁻¹ : Fˣ) : F),
      c + a * p * s * ((t₂ * t₃⁻¹ : Fˣ) : F) + s * ((t₁ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩, p⟩

private def refl12Right13 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ =>
    ⟨⟨a, b + s * ((t₂ * t₃⁻¹ : Fˣ) : F), c + a * s * ((t₂ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩, p⟩

private def refl23Right12 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ =>
    ⟨⟨a - q * s * ((t₁ * t₂⁻¹ : Fˣ) : F), b, c + s * ((t₁ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩, q⟩

private def refl23Right23 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨n, t, q⟩ => ⟨n, t, q + s⟩

private def refl23Right13 (s : F) :
    (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → (F × F × F) × (Fˣ × Fˣ × Fˣ) × F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ =>
    ⟨⟨a + s * ((t₁ * t₂⁻¹ : Fˣ) : F), b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩

end ReflectionCells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section BorelCell

private def borelRight12 (s : F) : (F × F × F) × (Fˣ × Fˣ × Fˣ) → (F × F × F) × (Fˣ × Fˣ × Fˣ) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ => ⟨⟨a + s * ((t₁ * t₂⁻¹ : Fˣ) : F), b, c⟩, ⟨t₁, t₂, t₃⟩⟩

private def borelRight23 (s : F) : (F × F × F) × (Fˣ × Fˣ × Fˣ) → (F × F × F) × (Fˣ × Fˣ × Fˣ) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ =>
    ⟨⟨a, b + s * ((t₂ * t₃⁻¹ : Fˣ) : F), c + a * s * ((t₂ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩⟩

private def borelRight13 (s : F) : (F × F × F) × (Fˣ × Fˣ × Fˣ) → (F × F × F) × (Fˣ × Fˣ × Fˣ) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ => ⟨⟨a, b, c + s * ((t₁ * t₃⁻¹ : Fˣ) : F)⟩, ⟨t₁, t₂, t₃⟩⟩

private def borelInvolution : (F × F × F) × (Fˣ × Fˣ × Fˣ) → (F × F × F) × (Fˣ × Fˣ × Fˣ) :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ =>
    ⟨⟨b * ((t₃ * t₂⁻¹ : Fˣ) : F), a * ((t₂ * t₁⁻¹ : Fˣ) : F), c * ((t₃ * t₁⁻¹ : Fˣ) : F)⟩,
      ⟨t₃, t₂, t₁⟩⟩

private theorem borelInvolution_involutive : Function.Involutive (borelInvolution (F := F)) := by
  rintro ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩
  have h₁ : (t₁ : F) ≠ 0 := t₁.ne_zero
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  have h₃ : (t₃ : F) ≠ 0 := t₃.ne_zero
  dsimp only [borelInvolution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

private theorem borelInvolution_torus (n : F × F × F) (t₁ t₂ t₃ : Fˣ) :
    (borelInvolution (n, (t₁, t₂, t₃))).2 = (t₃, t₂, t₁) := by
  obtain ⟨a, b, c⟩ := n
  rfl

private theorem borelInvolution_of_eq (a b c : F) (t₁ t₂ t₃ : Fˣ) (h₁₂ : t₁ = t₂) (h₂₃ : t₂ = t₃) :
    borelInvolution ((a, b, c), (t₁, t₂, t₃)) = ((b, a, c), (t₁, t₂, t₃)) := by
  have h₁ : (t₁ : F) ≠ 0 := t₁.ne_zero
  subst h₂₃
  subst h₁₂
  dsimp only [borelInvolution]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ext <;> (try field_simp) <;> first | rfl | ring1

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section

set_option autoImplicit false

namespace WhittakerCoinvariantsGL3

section Algebra

variable {F : Type*} [Field F]

private def torusRatio12 (t : Fˣ × Fˣ × Fˣ) : F := ((t.1 * t.2.1⁻¹ : Fˣ) : F)

private def torusRatio21 (t : Fˣ × Fˣ × Fˣ) : F := ((t.2.1 * t.1⁻¹ : Fˣ) : F)

private def torusRatio23 (t : Fˣ × Fˣ × Fˣ) : F := ((t.2.1 * t.2.2⁻¹ : Fˣ) : F)

private def torusRatio32 (t : Fˣ × Fˣ × Fˣ) : F := ((t.2.2 * t.2.1⁻¹ : Fˣ) : F)

private def torusRatio13 (t : Fˣ × Fˣ × Fˣ) : F := ((t.1 * t.2.2⁻¹ : Fˣ) : F)

private def torusRatio31 (t : Fˣ × Fˣ × Fˣ) : F := ((t.2.2 * t.1⁻¹ : Fˣ) : F)

private theorem torus_prodMap {N T R : Type*} (f : N → N) (x : N × T × R) : (Prod.map f id x).2.1 = x.2.1 :=
  rfl

private theorem snd_prodMap {N T : Type*} (f : N → N) (x : N × T) : (Prod.map f id x).2 = x.2 :=
  rfl

private theorem bigCellRight12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellRight12 (-s) (bigCellRight12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  dsimp only [bigCellRight12]
  ext <;> first | rfl | ring1

private theorem bigCellRight12_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    (bigCellRight12 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  rfl

private theorem bigCellRight23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellRight23 (-s) (bigCellRight23 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  dsimp only [bigCellRight23]
  ext <;> first | rfl | ring1

private theorem bigCellRight23_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    (bigCellRight23 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  rfl

private theorem bigCellRight13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellRight13 (-s) (bigCellRight13 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  dsimp only [bigCellRight13]
  ext <;> first | rfl | ring1

private theorem bigCellRight13_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    (bigCellRight13 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  rfl

private theorem cycle123Right12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle123Right12 (-s) (cycle123Right12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  dsimp only [cycle123Right12]
  ext <;> first | rfl | ring1

private theorem cycle123Right23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle123Right23 (-s) (cycle123Right23 s x) = x := by
  obtain ⟨n, t, ⟨q, r⟩⟩ := x
  dsimp only [cycle123Right23]
  ext <;> first | rfl | ring1

private theorem cycle123Right13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle123Right13 (-s) (cycle123Right13 s x) = x := by
  obtain ⟨n, t, ⟨q, r⟩⟩ := x
  dsimp only [cycle123Right13]
  ext <;> first | rfl | ring1

private theorem cycle123Right12_torus (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle123Right12 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  rfl

private theorem cycle123Right23_torus (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle123Right23 s x).2.1 = x.2.1 := by
  obtain ⟨n, t, ⟨q, r⟩⟩ := x
  rfl

private theorem cycle123Right13_torus (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle123Right13 s x).2.1 = x.2.1 := by
  obtain ⟨n, t, ⟨q, r⟩⟩ := x
  rfl

private theorem cycle132Right12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle132Right12 (-s) (cycle132Right12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  dsimp only [cycle132Right12]
  ext <;> first | rfl | ring1

private theorem cycle132Right12_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle132Right12 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  rfl

private theorem cycle132Right23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle132Right23 (-s) (cycle132Right23 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  dsimp only [cycle132Right23]
  ext <;> first | rfl | ring1

private theorem cycle132Right23_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle132Right23 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  rfl

private theorem cycle132Right13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycle132Right13 (-s) (cycle132Right13 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  dsimp only [cycle132Right13]
  ext <;> first | rfl | ring1

private theorem cycle132Right13_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    (cycle132Right13 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  rfl

private theorem refl12Right12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl12Right12 (-s) (refl12Right12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  dsimp only [refl12Right12]
  ext <;> first | rfl | ring1

private theorem refl12Right12_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl12Right12 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  rfl

private theorem refl12Right23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl12Right23 (-s) (refl12Right23 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  dsimp only [refl12Right23]
  ext <;> first | rfl | ring1

private theorem refl12Right23_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl12Right23 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  rfl

private theorem refl12Right13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl12Right13 (-s) (refl12Right13 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  dsimp only [refl12Right13]
  ext <;> first | rfl | ring1

private theorem refl12Right13_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl12Right13 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  rfl

private theorem refl23Right12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl23Right12 (-s) (refl23Right12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  dsimp only [refl23Right12]
  ext <;> first | rfl | ring1

private theorem refl23Right12_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl23Right12 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  rfl

private theorem refl23Right23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl23Right23 (-s) (refl23Right23 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  dsimp only [refl23Right23]
  ext <;> first | rfl | ring1

private theorem refl23Right23_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl23Right23 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  rfl

private theorem refl23Right13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    refl23Right13 (-s) (refl23Right13 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  dsimp only [refl23Right13]
  ext <;> first | rfl | ring1

private theorem refl23Right13_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    (refl23Right13 s x).2.1 = x.2.1 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  rfl

private theorem borelRight12_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelRight12 (-s) (borelRight12 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  dsimp only [borelRight12]
  ext <;> first | rfl | ring1

private theorem borelRight12_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    (borelRight12 s x).2 = x.2 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  rfl

private theorem borelRight23_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelRight23 (-s) (borelRight23 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  dsimp only [borelRight23]
  ext <;> first | rfl | ring1

private theorem borelRight23_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    (borelRight23 s x).2 = x.2 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  rfl

private theorem borelRight13_neg_comp (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelRight13 (-s) (borelRight13 s x) = x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  dsimp only [borelRight13]
  ext <;> first | rfl | ring1

private theorem borelRight13_torus (s : F)
    (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    (borelRight13 s x).2 = x.2 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  rfl

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

@[scoped fun_prop]
private theorem continuous_torusRatio12 : Continuous (torusRatio12 (F := F)) :=
  Units.continuous_val.comp (continuous_fst.mul (continuous_fst.comp continuous_snd).inv)

@[scoped fun_prop]
private theorem continuous_torusRatio21 : Continuous (torusRatio21 (F := F)) :=
  Units.continuous_val.comp ((continuous_fst.comp continuous_snd).mul continuous_fst.inv)

@[scoped fun_prop]
private theorem continuous_torusRatio23 : Continuous (torusRatio23 (F := F)) :=
  Units.continuous_val.comp
    ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd).inv)

@[scoped fun_prop]
private theorem continuous_torusRatio32 : Continuous (torusRatio32 (F := F)) :=
  Units.continuous_val.comp
    ((continuous_snd.comp continuous_snd).mul (continuous_fst.comp continuous_snd).inv)

@[scoped fun_prop]
private theorem continuous_torusRatio13 : Continuous (torusRatio13 (F := F)) :=
  Units.continuous_val.comp (continuous_fst.mul (continuous_snd.comp continuous_snd).inv)

@[scoped fun_prop]
private theorem continuous_torusRatio31 : Continuous (torusRatio31 (F := F)) :=
  Units.continuous_val.comp ((continuous_snd.comp continuous_snd).mul continuous_fst.inv)

private theorem continuous_leftRoot12 (s : F) : Continuous (leftRoot12 (F := F) s) := by
  have h : leftRoot12 (F := F) s = fun x => (x.1 + s, x.2.1, x.2.2 + x.2.1 * s) := by
    funext ⟨a, b, c⟩
    rfl
  rw [h]
  fun_prop

private theorem continuous_leftRoot23 (s : F) : Continuous (leftRoot23 (F := F) s) := by
  have h : leftRoot23 (F := F) s = fun x => (x.1, x.2.1 + s, x.2.2) := by
    funext ⟨a, b, c⟩
    rfl
  rw [h]
  fun_prop

private theorem continuous_leftRoot13 (s : F) : Continuous (leftRoot13 (F := F) s) := by
  have h : leftRoot13 (F := F) s = fun x => (x.1, x.2.1, x.2.2 + s) := by
    funext ⟨a, b, c⟩
    rfl
  rw [h]
  fun_prop

private def leftRoot12Homeomorph (s : F) : (F × F × F) ≃ₜ (F × F × F) where
  toFun := leftRoot12 s
  invFun := leftRoot12 (-s)
  left_inv := leftRoot12_neg_comp s
  right_inv x := by simpa using leftRoot12_neg_comp (-s) x
  continuous_toFun := continuous_leftRoot12 s
  continuous_invFun := continuous_leftRoot12 (-s)

private def leftRoot23Homeomorph (s : F) : (F × F × F) ≃ₜ (F × F × F) where
  toFun := leftRoot23 s
  invFun := leftRoot23 (-s)
  left_inv := leftRoot23_neg_comp s
  right_inv x := by simpa using leftRoot23_neg_comp (-s) x
  continuous_toFun := continuous_leftRoot23 s
  continuous_invFun := continuous_leftRoot23 (-s)

private def leftRoot13Homeomorph (s : F) : (F × F × F) ≃ₜ (F × F × F) where
  toFun := leftRoot13 s
  invFun := leftRoot13 (-s)
  left_inv := leftRoot13_neg_comp s
  right_inv x := by simpa using leftRoot13_neg_comp (-s) x
  continuous_toFun := continuous_leftRoot13 s
  continuous_invFun := continuous_leftRoot13 (-s)

private theorem continuous_bigCellRight12 (s : F) : Continuous (bigCellRight12 (F := F) s) := by
  have h : bigCellRight12 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1 + s, x.2.2.2.1,
      x.2.2.2.2)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def bigCellRight12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) where
  toFun := bigCellRight12 s
  invFun := bigCellRight12 (-s)
  left_inv := bigCellRight12_neg_comp s
  right_inv x := by simpa using bigCellRight12_neg_comp (-s) x
  continuous_toFun := continuous_bigCellRight12 s
  continuous_invFun := continuous_bigCellRight12 (-s)

private theorem continuous_bigCellRight23 (s : F) : Continuous (bigCellRight23 (F := F) s) := by
  have h : bigCellRight23 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1, x.2.2.2.1 + s,
      x.2.2.2.2 + x.2.2.1 * s)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def bigCellRight23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) where
  toFun := bigCellRight23 s
  invFun := bigCellRight23 (-s)
  left_inv := bigCellRight23_neg_comp s
  right_inv x := by simpa using bigCellRight23_neg_comp (-s) x
  continuous_toFun := continuous_bigCellRight23 s
  continuous_invFun := continuous_bigCellRight23 (-s)

private theorem continuous_bigCellRight13 (s : F) : Continuous (bigCellRight13 (F := F) s) := by
  have h : bigCellRight13 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1, x.2.2.2.1,
      x.2.2.2.2 + s)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def bigCellRight13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) where
  toFun := bigCellRight13 s
  invFun := bigCellRight13 (-s)
  left_inv := bigCellRight13_neg_comp s
  right_inv x := by simpa using bigCellRight13_neg_comp (-s) x
  continuous_toFun := continuous_bigCellRight13 s
  continuous_invFun := continuous_bigCellRight13 (-s)

omit [IsTopologicalRing F] in
private theorem continuous_bigCellInvolution : Continuous (bigCellInvolution (F := F)) := by
  have h : bigCellInvolution (F := F) = fun x =>
      ((x.2.2.2.1, x.2.2.1, x.2.2.2.2), x.2.1, (x.1.2.1, x.1.1, x.1.2.2)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def bigCellInvolutionHomeomorph : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F))
    ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) where
  toFun := bigCellInvolution
  invFun := bigCellInvolution
  left_inv := bigCellInvolution_involutive
  right_inv := bigCellInvolution_involutive
  continuous_toFun := continuous_bigCellInvolution
  continuous_invFun := continuous_bigCellInvolution

omit [IsTopologicalRing F] in
private theorem continuous_bigCellTorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) => x.2.1 := by
  fun_prop

private theorem continuous_cycle123Right12 (s : F) : Continuous (cycle123Right12 (F := F) s) := by
  have h : cycle123Right12 (F := F) s = fun x =>
      ((x.1.1, x.1.2.1 + s * torusRatio23 x.2.1, x.1.2.2 + x.1.1 * s * torusRatio23 x.2.1), x.2.1,
        (x.2.2.1, x.2.2.2 - x.2.2.1 * s)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private theorem continuous_cycle123Right23 (s : F) : Continuous (cycle123Right23 (F := F) s) := by
  have h : cycle123Right23 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1 + s, x.2.2.2)) := by
    funext ⟨n, t, ⟨q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private theorem continuous_cycle123Right13 (s : F) : Continuous (cycle123Right13 (F := F) s) := by
  have h : cycle123Right13 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1, x.2.2.2 + s)) := by
    funext ⟨n, t, ⟨q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private theorem continuous_cycle123Involution : Continuous (cycle123Involution (F := F)) := by
  have h : cycle123Involution (F := F) = fun x =>
      ((x.2.2.1, x.1.2.1 * torusRatio32 x.2.1, x.1.2.1 * x.2.2.1 * torusRatio32 x.2.1 + x.2.2.2),
        (x.2.1.1, x.2.1.2.2, x.2.1.2.1), (x.1.1, x.1.2.2 - x.1.1 * x.1.2.1)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def cycle123Right12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle123Right12 s
  invFun := cycle123Right12 (-s)
  left_inv := cycle123Right12_neg_comp s
  right_inv x := by simpa using cycle123Right12_neg_comp (-s) x
  continuous_toFun := continuous_cycle123Right12 s
  continuous_invFun := continuous_cycle123Right12 (-s)

private def cycle123Right23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle123Right23 s
  invFun := cycle123Right23 (-s)
  left_inv := cycle123Right23_neg_comp s
  right_inv x := by simpa using cycle123Right23_neg_comp (-s) x
  continuous_toFun := continuous_cycle123Right23 s
  continuous_invFun := continuous_cycle123Right23 (-s)

private def cycle123Right13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle123Right13 s
  invFun := cycle123Right13 (-s)
  left_inv := cycle123Right13_neg_comp s
  right_inv x := by simpa using cycle123Right13_neg_comp (-s) x
  continuous_toFun := continuous_cycle123Right13 s
  continuous_invFun := continuous_cycle123Right13 (-s)

private def cycle123InvolutionHomeomorph :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle123Involution
  invFun := cycle123Involution
  left_inv := cycle123Involution_involutive
  right_inv := cycle123Involution_involutive
  continuous_toFun := continuous_cycle123Involution
  continuous_invFun := continuous_cycle123Involution

omit [IsTopologicalRing F] in
private theorem continuous_cycle123TorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1 := by
  fun_prop

private theorem continuous_cycle132Right12 (s : F) : Continuous (cycle132Right12 (F := F) s) := by
  have h : cycle132Right12 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1 + s, x.2.2.2)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def cycle132Right12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle132Right12 s
  invFun := cycle132Right12 (-s)
  left_inv := cycle132Right12_neg_comp s
  right_inv x := by simpa using cycle132Right12_neg_comp (-s) x
  continuous_toFun := continuous_cycle132Right12 s
  continuous_invFun := continuous_cycle132Right12 (-s)

private theorem continuous_cycle132Right23 (s : F) : Continuous (cycle132Right23 (F := F) s) := by
  have h : cycle132Right23 (F := F) s = fun x =>
      ((x.1.1 + s * torusRatio12 x.2.1, x.1.2.1, x.1.2.2), x.2.1, (x.2.2.1,
          x.2.2.2 + x.2.2.1 * s)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def cycle132Right23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle132Right23 s
  invFun := cycle132Right23 (-s)
  left_inv := cycle132Right23_neg_comp s
  right_inv x := by simpa using cycle132Right23_neg_comp (-s) x
  continuous_toFun := continuous_cycle132Right23 s
  continuous_invFun := continuous_cycle132Right23 (-s)

private theorem continuous_cycle132Right13 (s : F) : Continuous (cycle132Right13 (F := F) s) := by
  have h : cycle132Right13 (F := F) s = fun x => (x.1, x.2.1, (x.2.2.1, x.2.2.2 + s)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def cycle132Right13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle132Right13 s
  invFun := cycle132Right13 (-s)
  left_inv := cycle132Right13_neg_comp s
  right_inv x := by simpa using cycle132Right13_neg_comp (-s) x
  continuous_toFun := continuous_cycle132Right13 s
  continuous_invFun := continuous_cycle132Right13 (-s)

private theorem continuous_cycle132Involution : Continuous (cycle132Involution (F := F)) := by
  have h : cycle132Involution (F := F) = fun x =>
      ((x.1.1 * torusRatio21 x.2.1, x.2.2.1, x.2.2.2), (x.2.1.2.1, x.2.1.1, x.2.1.2.2), (x.1.2.1,
          x.1.2.2)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩
    rfl
  rw [h]
  fun_prop

private def cycle132InvolutionHomeomorph : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F))
    ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) where
  toFun := cycle132Involution
  invFun := cycle132Involution
  left_inv := cycle132Involution_involutive
  right_inv := cycle132Involution_involutive
  continuous_toFun := continuous_cycle132Involution
  continuous_invFun := continuous_cycle132Involution

omit [IsTopologicalRing F] in
private theorem continuous_cycle132TorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1 := by
  fun_prop

private theorem continuous_refl12Right12 (s : F) : Continuous (refl12Right12 (F := F) s) := by
  have h : refl12Right12 (F := F) s = fun x => (x.1, x.2.1, x.2.2 + s) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩
    rfl
  rw [h]
  fun_prop

private def refl12Right12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl12Right12 s
  invFun := refl12Right12 (-s)
  left_inv := refl12Right12_neg_comp s
  right_inv x := by simpa using refl12Right12_neg_comp (-s) x
  continuous_toFun := continuous_refl12Right12 s
  continuous_invFun := continuous_refl12Right12 (-s)

private theorem continuous_refl12Right23 (s : F) : Continuous (refl12Right23 (F := F) s) := by
  have h : refl12Right23 (F := F) s = fun x =>
      ((x.1.1, x.1.2.1 + x.2.2 * s * torusRatio23 x.2.1,
        x.1.2.2 + x.1.1 * x.2.2 * s * torusRatio23 x.2.1 + s * torusRatio13 x.2.1), x.2.1,
            x.2.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩
    rfl
  rw [h]
  fun_prop

private def refl12Right23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl12Right23 s
  invFun := refl12Right23 (-s)
  left_inv := refl12Right23_neg_comp s
  right_inv x := by simpa using refl12Right23_neg_comp (-s) x
  continuous_toFun := continuous_refl12Right23 s
  continuous_invFun := continuous_refl12Right23 (-s)

private theorem continuous_refl12Right13 (s : F) : Continuous (refl12Right13 (F := F) s) := by
  have h : refl12Right13 (F := F) s = fun x =>
      ((x.1.1, x.1.2.1 + s * torusRatio23 x.2.1, x.1.2.2 + x.1.1 * s * torusRatio23 x.2.1), x.2.1,
          x.2.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩
    rfl
  rw [h]
  fun_prop

private def refl12Right13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl12Right13 s
  invFun := refl12Right13 (-s)
  left_inv := refl12Right13_neg_comp s
  right_inv x := by simpa using refl12Right13_neg_comp (-s) x
  continuous_toFun := continuous_refl12Right13 s
  continuous_invFun := continuous_refl12Right13 (-s)

omit [IsTopologicalRing F] in
private theorem continuous_refl12TorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F => x.2.1 := by
  fun_prop

private theorem continuous_refl23Right12 (s : F) : Continuous (refl23Right12 (F := F) s) := by
  have h : refl23Right12 (F := F) s = fun x =>
      ((x.1.1 - x.2.2 * s * torusRatio12 x.2.1, x.1.2.1, x.1.2.2 + s * torusRatio13 x.2.1), x.2.1,
          x.2.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩
    rfl
  rw [h]
  fun_prop

private def refl23Right12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl23Right12 s
  invFun := refl23Right12 (-s)
  left_inv := refl23Right12_neg_comp s
  right_inv x := by simpa using refl23Right12_neg_comp (-s) x
  continuous_toFun := continuous_refl23Right12 s
  continuous_invFun := continuous_refl23Right12 (-s)

private theorem continuous_refl23Right23 (s : F) : Continuous (refl23Right23 (F := F) s) := by
  have h : refl23Right23 (F := F) s = fun x => (x.1, x.2.1, x.2.2 + s) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩
    rfl
  rw [h]
  fun_prop

private def refl23Right23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl23Right23 s
  invFun := refl23Right23 (-s)
  left_inv := refl23Right23_neg_comp s
  right_inv x := by simpa using refl23Right23_neg_comp (-s) x
  continuous_toFun := continuous_refl23Right23 s
  continuous_invFun := continuous_refl23Right23 (-s)

private theorem continuous_refl23Right13 (s : F) : Continuous (refl23Right13 (F := F) s) := by
  have h : refl23Right13 (F := F) s = fun x => ((x.1.1 + s * torusRatio12 x.2.1, x.1.2.1, x.1.2.2),
      x.2.1, x.2.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩
    rfl
  rw [h]
  fun_prop

private def refl23Right13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) where
  toFun := refl23Right13 s
  invFun := refl23Right13 (-s)
  left_inv := refl23Right13_neg_comp s
  right_inv x := by simpa using refl23Right13_neg_comp (-s) x
  continuous_toFun := continuous_refl23Right13 s
  continuous_invFun := continuous_refl23Right13 (-s)

omit [IsTopologicalRing F] in
private theorem continuous_refl23TorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F => x.2.1 := by
  fun_prop

private theorem continuous_borelRight12 (s : F) : Continuous (borelRight12 (F := F) s) := by
  have h : borelRight12 (F := F) s = fun x => ((x.1.1 + s * torusRatio12 x.2, x.1.2.1, x.1.2.2),
      x.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩
    rfl
  rw [h]
  fun_prop

private def borelRight12Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ)) where
  toFun := borelRight12 s
  invFun := borelRight12 (-s)
  left_inv := borelRight12_neg_comp s
  right_inv x := by simpa using borelRight12_neg_comp (-s) x
  continuous_toFun := continuous_borelRight12 s
  continuous_invFun := continuous_borelRight12 (-s)

private theorem continuous_borelRight23 (s : F) : Continuous (borelRight23 (F := F) s) := by
  have h : borelRight23 (F := F) s = fun x =>
      ((x.1.1, x.1.2.1 + s * torusRatio23 x.2, x.1.2.2 + x.1.1 * s * torusRatio23 x.2), x.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩
    rfl
  rw [h]
  fun_prop

private def borelRight23Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ)) where
  toFun := borelRight23 s
  invFun := borelRight23 (-s)
  left_inv := borelRight23_neg_comp s
  right_inv x := by simpa using borelRight23_neg_comp (-s) x
  continuous_toFun := continuous_borelRight23 s
  continuous_invFun := continuous_borelRight23 (-s)

private theorem continuous_borelRight13 (s : F) : Continuous (borelRight13 (F := F) s) := by
  have h : borelRight13 (F := F) s = fun x => ((x.1.1, x.1.2.1, x.1.2.2 + s * torusRatio13 x.2),
      x.2) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩
    rfl
  rw [h]
  fun_prop

private def borelRight13Homeomorph (s : F) :
    ((F × F × F) × (Fˣ × Fˣ × Fˣ)) ≃ₜ
      ((F × F × F) × (Fˣ × Fˣ × Fˣ)) where
  toFun := borelRight13 s
  invFun := borelRight13 (-s)
  left_inv := borelRight13_neg_comp s
  right_inv x := by simpa using borelRight13_neg_comp (-s) x
  continuous_toFun := continuous_borelRight13 s
  continuous_invFun := continuous_borelRight13 (-s)

private theorem continuous_borelInvolution : Continuous (borelInvolution (F := F)) := by
  have h : borelInvolution (F := F) = fun x =>
      ((x.1.2.1 * torusRatio32 x.2, x.1.1 * torusRatio21 x.2, x.1.2.2 * torusRatio31 x.2),
        (x.2.2.2, x.2.2.1, x.2.1)) := by
    funext ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩
    rfl
  rw [h]
  fun_prop

private def borelInvolutionHomeomorph : ((F × F × F) × (Fˣ × Fˣ × Fˣ))
    ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ)) where
  toFun := borelInvolution
  invFun := borelInvolution
  left_inv := borelInvolution_involutive
  right_inv := borelInvolution_involutive
  continuous_toFun := continuous_borelInvolution
  continuous_invFun := continuous_borelInvolution

omit [IsTopologicalRing F] in
private theorem continuous_borelTorusProjection :
    Continuous fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) => x.2 := by
  fun_prop

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

noncomputable section

open Function Set LanglandsTunnell.TateLocal

namespace SchwartzBruhatIntegral

section General

variable {X : Type*} [TopologicalSpace X]

private def compLin (e : X ≃ₜ X) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun f := f ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem compLin_apply (e : X ≃ₜ X) (f : X → ℂ) : compLin e f = f ∘ e :=
  rfl

private theorem isLocallyConstant_indicator_clopen {X : Type*} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (W.indicator f) := by
  have h : W.indicator f = fun x => f x * W.indicator (fun _ => (1 : ℂ)) x := by
    funext x
    by_cases hx : x ∈ W
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [h]
  refine hf.mul ?_
  intro s
  classical
  have : (W.indicator fun _ => (1 : ℂ)) ⁻¹' s =
      (if (1 : ℂ) ∈ s then W else ∅) ∪ (if (0 : ℂ) ∈ s then Wᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ W <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
      simp [Set.indicator, hx, h1, h0]
  rw [this]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact hW.isOpen
    · exact isOpen_empty
  · split_ifs
    · exact hW.compl.isOpen
    · exact isOpen_empty

private theorem indicator_preimage_mem {Y : Type*} [TopologicalSpace Y] {φ : X → Y} (hφ : Continuous φ) {f : X → ℂ}
    (hf : IsSchwartzBruhat f) {V : Set Y} (hV : IsClopen V) : IsSchwartzBruhat ((φ ⁻¹' V).indicator f) := by
  refine ⟨isLocallyConstant_indicator_clopen (hV.preimage hφ) hf.1, ?_⟩
  refine hf.2.mono ?_
  rw [Set.support_indicator]
  exact Set.inter_subset_right

private theorem compLin_indicator_preimage {Y : Type*} {φ : X → Y} {P : Type*} (τ : P → X ≃ₜ X)
    (hτ : ∀ t x, φ (τ t x) = φ x) (t : P) (V : Set Y) (g : X → ℂ) :
    compLin (τ t) ((φ ⁻¹' V).indicator g) = (φ ⁻¹' V).indicator (compLin (τ t) g) := by
  funext p
  by_cases hp : p ∈ φ ⁻¹' V
  · have hp' : τ t p ∈ φ ⁻¹' V := by
      show φ (τ t p) ∈ V
      rw [hτ t p]
      exact hp
    rw [compLin_apply, Function.comp_apply, Set.indicator_of_mem hp', Set.indicator_of_mem hp, compLin_apply,
      Function.comp_apply]
  · have hp' : τ t p ∉ φ ⁻¹' V := by
      show φ (τ t p) ∉ V
      rw [hτ t p]
      exact hp
    rw [compLin_apply, Function.comp_apply, Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]

private theorem comp_shear_sub_mem_coinvariants {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U) {φ : X → Y}
    (hφ : Continuous φ) {P : Type*} (τ : P → X ≃ₜ X) (hτ : ∀ t x, φ (τ t x) = φ x) (σ : X ≃ₜ X) {c : Y → P}
    (hσ : ∀ x, σ x = τ (c (φ x)) x) {f : X → ℂ} (hf : IsSchwartzBruhat f) :
    f ∘ σ - f ∈ Localisation.coinvariants (fun t => compLin (τ t)) (sbSubmodule X) := by
  refine Localisation.mem_coinvariants_of_forall_fibre φ (fun t => compLin (τ t)) (sbSubmodule X) hφ hY
    (fun g hg => hg.1) (fun g hg => hg.2) ?_ ?_ ?_ ?_ ?_
  ·
    intro g hg V hV
    exact indicator_preimage_mem hφ hg hV
  ·
    intro t g hg
    exact isSchwartzBruhat_comp_homeo hg (τ t)
  ·
    intro t V hV g hg
    exact compLin_indicator_preimage τ hτ t V g
  ·
    exact (sbSubmodule X).sub_mem (isSchwartzBruhat_comp_homeo hf σ) hf
  ·
    intro y _
    refine ⟨compLin (τ (c y)) f - f, Localisation.sub_mem_coinvariants _ _ (c y) hf, ?_⟩
    intro x hx
    subst hx
    show f (σ x) - f x = f (τ (c (φ x)) x) - f x
    rw [hσ x]

private theorem apply_comp_shear_eq {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U) {φ : X → Y}
    (hφ : Continuous φ) {P : Type*} (τ : P → X ≃ₜ X) (hτ : ∀ t x, φ (τ t x) = φ x) (σ : X ≃ₜ X) {c : Y → P}
    (hσ : ∀ x, σ x = τ (c (φ x)) x) (T : (X → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ t : P, ∀ g : X → ℂ, IsSchwartzBruhat g → T (compLin (τ t) g) = T g) {f : X → ℂ}
    (hf : IsSchwartzBruhat f) : T (f ∘ σ) = T f := by
  have h0 := Localisation.apply_eq_zero_of_mem_coinvariants (fun t => compLin (τ t)) (sbSubmodule X) T
    (fun t g hg => hT t g hg) (comp_shear_sub_mem_coinvariants hY hφ τ hτ σ hσ hf)
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end General
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Shear

variable {F Y : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [TopologicalSpace Y]

private def shiftHomeo (t : F) : F × Y ≃ₜ F × Y :=
  (Homeomorph.addRight t).prodCongr (Homeomorph.refl Y)

private theorem shiftHomeo_apply (t : F) (p : F × Y) : (shiftHomeo t : F × Y ≃ₜ F × Y) p = (p.1 + t, p.2) :=
  rfl

private theorem snd_shiftHomeo (t : F) (p : F × Y) : ((shiftHomeo t : F × Y ≃ₜ F × Y) p).2 = p.2 :=
  rfl

private def shearHomeo {c : Y → F} (hc : Continuous c) : F × Y ≃ₜ F × Y where
  toFun p := (p.1 + c p.2, p.2)
  invFun p := (p.1 - c p.2, p.2)
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp
  continuous_toFun := by
    exact (continuous_fst.add (hc.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := by
    exact (continuous_fst.sub (hc.comp continuous_snd)).prodMk continuous_snd

private theorem shearHomeo_apply {c : Y → F} (hc : Continuous c) (p : F × Y) :
    (shearHomeo hc : F × Y ≃ₜ F × Y) p = (p.1 + c p.2, p.2) :=
  rfl

private theorem shearHomeo_eq_shiftHomeo {c : Y → F} (hc : Continuous c) (p : F × Y) :
    (shearHomeo hc : F × Y ≃ₜ F × Y) p = (shiftHomeo (c p.2) : F × Y ≃ₜ F × Y) p :=
  rfl

private def translationOps : F → (F × Y → ℂ) →ₗ[ℂ] (F × Y → ℂ) :=
  fun t => compLin (shiftHomeo t)

private theorem translationOps_apply (t : F) (f : F × Y → ℂ) (p : F × Y) :
    translationOps t f p = f (p.1 + t, p.2) :=
  rfl

private theorem comp_shearHomeo_sub_mem_coinvariants [T2Space Y]
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    {c : Y → F} (hc : Continuous c) {f : F × Y → ℂ} (hf : IsSchwartzBruhat f) :
    f ∘ (shearHomeo hc : F × Y ≃ₜ F × Y) - f ∈
      Localisation.coinvariants (translationOps (F := F) (Y := Y)) (sbSubmodule (F × Y)) :=
  comp_shear_sub_mem_coinvariants hY continuous_snd (shiftHomeo (F := F) (Y := Y)) snd_shiftHomeo (shearHomeo hc)
    (shearHomeo_eq_shiftHomeo hc) hf

private theorem apply_comp_shearHomeo_eq [T2Space Y]
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    {c : Y → F} (hc : Continuous c) (T : (F × Y → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ t : F, ∀ g : F × Y → ℂ, IsSchwartzBruhat g → T (translationOps t g) = T g) {f : F × Y → ℂ}
    (hf : IsSchwartzBruhat f) : T (f ∘ (shearHomeo hc : F × Y ≃ₜ F × Y)) = T f :=
  apply_comp_shear_eq hY continuous_snd (shiftHomeo (F := F) (Y := Y)) snd_shiftHomeo (shearHomeo hc)
    (shearHomeo_eq_shiftHomeo hc) T hT hf

end Shear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end SchwartzBruhatIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatIntegral LanglandsTunnell.TateLocal

namespace WhittakerCoinvariantsGL3

section Middle

variable {K₁ Y K₂ : Type*}

private def opOfMapMid (c : ℂ) (R : K₁ × (Y × K₂) → K₁ × (Y × K₂)) : FibrewiseOp (K₁ × K₂) Y where
  coeff := fun _ => c
  map := fun y k => ((R (k.1, (y, k.2))).1, (R (k.1, (y, k.2))).2.2)

private theorem opOfMapMid_coeff (c : ℂ) (R : K₁ × (Y × K₂) → K₁ × (Y × K₂)) (y : Y) :
    (opOfMapMid c R).coeff y = c :=
  rfl

private theorem opOfMapMid_map (c : ℂ) (R : K₁ × (Y × K₂) → K₁ × (Y × K₂)) (y : Y) (k : K₁ × K₂) :
    (opOfMapMid c R).map y k = ((R (k.1, (y, k.2))).1, (R (k.1, (y, k.2))).2.2) :=
  rfl

private theorem toLinMid_opOfMapMid (c : ℂ) {R : K₁ × (Y × K₂) → K₁ × (Y × K₂)}
    (hR : ∀ x, (R x).2.1 = x.2.1) (f : K₁ × (Y × K₂) → ℂ) :
    (opOfMapMid c R).toLinMid f = fun x => c * f (R x) := by
  funext x
  obtain ⟨k₁, y, k₂⟩ := x
  show _ = c * f (R (k₁, (y, k₂)))
  have h1 : (opOfMapMid c R).toLinMid f (k₁, (y, k₂)) =
      c * f ((R (k₁, (y, k₂))).1, (y, (R (k₁, (y, k₂))).2.2)) := rfl
  have h2 : ((R (k₁, (y, k₂))).1, (y, (R (k₁, (y, k₂))).2.2)) = R (k₁, (y, k₂)) :=
    Prod.ext rfl (Prod.ext (hR (k₁, (y, k₂))).symm rfl)
  rw [h1, h2]

private theorem fibreRelation_opOfMapMid (c : ℂ) (R : K₁ × (Y × K₂) → K₁ × (Y × K₂)) (y : Y)
    (g : K₁ × K₂ → ℂ) :
    (opOfMapMid c R).fibreRelation y g =
      fun k => c * g ((R (k.1, (y, k.2))).1, (R (k.1, (y, k.2))).2.2) - g k :=
  rfl

variable [TopologicalSpace K₁] [TopologicalSpace Y] [TopologicalSpace K₂]

private theorem toLinMid_opOfMapMid_mem (c : ℂ) (R : K₁ × (Y × K₂) ≃ₜ K₁ × (Y × K₂))
    (hR : ∀ x, (R x).2.1 = x.2.1) (f : K₁ × (Y × K₂) → ℂ)
    (hf : f ∈ sbSubmodule (K₁ × (Y × K₂))) :
    (opOfMapMid c (R : K₁ × (Y × K₂) → K₁ × (Y × K₂))).toLinMid f ∈
      sbSubmodule (K₁ × (Y × K₂)) := by
  rw [toLinMid_opOfMapMid c hR]
  exact (sbSubmodule (K₁ × (Y × K₂))).smul_mem c (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hf) R)

omit [TopologicalSpace K₁] [TopologicalSpace Y] [TopologicalSpace K₂] in

private theorem toLinMid_opOfMapMid_indicator (c : ℂ) {R : K₁ × (Y × K₂) → K₁ × (Y × K₂)}
    (hR : ∀ x, (R x).2.1 = x.2.1) (V : Set Y) (f : K₁ × (Y × K₂) → ℂ) :
    (opOfMapMid c R).toLinMid (((fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' V).indicator f) =
      ((fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' V).indicator ((opOfMapMid c R).toLinMid f) := by
  rw [toLinMid_opOfMapMid c hR, toLinMid_opOfMapMid c hR]
  funext x
  by_cases hx : x ∈ (fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' V
  · have hx' : R x ∈ (fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' V := by
      show (R x).2.1 ∈ V
      rw [hR x]
      exact hx
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : R x ∉ (fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' V := by
      show (R x).2.1 ∉ V
      rw [hR x]
      exact hx
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]

private def fibreInclMid (y : Y) : K₁ × K₂ → K₁ × (Y × K₂) :=
  fun k => (k.1, (y, k.2))

private theorem continuous_fibreInclMid (y : Y) : Continuous (fibreInclMid (K₁ := K₁) (K₂ := K₂) y) := by
  unfold fibreInclMid
  fun_prop

private theorem isClosedEmbedding_fibreInclMid [T1Space Y] (y : Y) :
    Topology.IsClosedEmbedding (fibreInclMid (K₁ := K₁) (K₂ := K₂) y) := by
  have hl : Function.LeftInverse (fun x : K₁ × (Y × K₂) => (x.1, x.2.2)) (fibreInclMid y) :=
    fun k => rfl
  refine ⟨hl.isEmbedding (by fun_prop) (continuous_fibreInclMid y), ?_⟩
  have hr : Set.range (fibreInclMid (K₁ := K₁) (K₂ := K₂) y) =
      (fun x : K₁ × (Y × K₂) => x.2.1) ⁻¹' {y} := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      rfl
    · intro hx
      refine ⟨(x.1, x.2.2), ?_⟩
      obtain ⟨k₁, y', k₂⟩ := x
      have hy : y' = y := hx
      subst hy
      rfl
  rw [hr]
  exact (isClosed_singleton).preimage (by fun_prop)

private theorem isSchwartzBruhat_fibreMid [T1Space Y] {f : K₁ × (Y × K₂) → ℂ} (hf : IsSchwartzBruhat f)
    (y : Y) : IsSchwartzBruhat (fun k : K₁ × K₂ => f (k.1, (y, k.2))) :=
  ⟨hf.1.comp_continuous (continuous_fibreInclMid y),
    hf.2.comp_isClosedEmbedding (isClosedEmbedding_fibreInclMid y)⟩

end Middle
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Last

variable {K Y : Type*}

private def opOfMapLast (c : ℂ) (R : K × Y → K × Y) : FibrewiseOp K Y where
  coeff := fun _ => c
  map := fun y k => (R (k, y)).1

private theorem opOfMapLast_coeff (c : ℂ) (R : K × Y → K × Y) (y : Y) : (opOfMapLast c R).coeff y = c :=
  rfl

private theorem opOfMapLast_map (c : ℂ) (R : K × Y → K × Y) (y : Y) (k : K) :
    (opOfMapLast c R).map y k = (R (k, y)).1 :=
  rfl

private theorem toLin_opOfMapLast (c : ℂ) {R : K × Y → K × Y} (hR : ∀ x, (R x).2 = x.2) (f : K × Y → ℂ) :
    (opOfMapLast c R).toLin f = fun x => c * f (R x) := by
  funext x
  obtain ⟨k, y⟩ := x
  show _ = c * f (R (k, y))
  have h1 : (opOfMapLast c R).toLin f (k, y) = c * f ((R (k, y)).1, y) := rfl
  have h2 : ((R (k, y)).1, y) = R (k, y) := Prod.ext rfl (hR (k, y)).symm
  rw [h1, h2]

private theorem fibreRelation_opOfMapLast (c : ℂ) (R : K × Y → K × Y) (y : Y) (g : K → ℂ) :
    (opOfMapLast c R).fibreRelation y g = fun k => c * g (R (k, y)).1 - g k :=
  rfl

variable [TopologicalSpace K] [TopologicalSpace Y]

private theorem toLin_opOfMapLast_mem (c : ℂ) (R : K × Y ≃ₜ K × Y) (hR : ∀ x, (R x).2 = x.2)
    (f : K × Y → ℂ) (hf : f ∈ sbSubmodule (K × Y)) :
    (opOfMapLast c (R : K × Y → K × Y)).toLin f ∈ sbSubmodule (K × Y) := by
  rw [toLin_opOfMapLast c hR]
  exact (sbSubmodule (K × Y)).smul_mem c (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hf) R)

omit [TopologicalSpace K] [TopologicalSpace Y] in
private theorem toLin_opOfMapLast_indicator (c : ℂ) {R : K × Y → K × Y} (hR : ∀ x, (R x).2 = x.2)
    (V : Set Y) (f : K × Y → ℂ) :
    (opOfMapLast c R).toLin ((Prod.snd ⁻¹' V).indicator f) =
      (Prod.snd ⁻¹' V).indicator ((opOfMapLast c R).toLin f) := by
  rw [toLin_opOfMapLast c hR, toLin_opOfMapLast c hR]
  funext x
  by_cases hx : x ∈ (Prod.snd ⁻¹' V : Set (K × Y))
  · have hx' : R x ∈ (Prod.snd ⁻¹' V : Set (K × Y)) := by
      show (R x).2 ∈ V
      rw [hR x]
      exact hx
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
  · have hx' : R x ∉ (Prod.snd ⁻¹' V : Set (K × Y)) := by
      show (R x).2 ∉ V
      rw [hR x]
      exact hx
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]

private theorem isClosedEmbedding_prodMkLeft [T1Space Y] (y : Y) :
    Topology.IsClosedEmbedding (fun k : K => (k, y)) := by
  refine ⟨isEmbedding_prodMkLeft y, ?_⟩
  have hr : Set.range (fun k : K => (k, y)) = (Prod.snd ⁻¹' {y} : Set (K × Y)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      rfl
    · intro hx
      refine ⟨x.1, ?_⟩
      obtain ⟨k, y'⟩ := x
      have hy : y' = y := hx
      subst hy
      rfl
  rw [hr]
  exact (isClosed_singleton).preimage continuous_snd

private theorem isSchwartzBruhat_fibreLast [T1Space Y] {f : K × Y → ℂ} (hf : IsSchwartzBruhat f) (y : Y) :
    IsSchwartzBruhat (fun k : K => f (k, y)) :=
  ⟨hf.1.comp_continuous (by fun_prop), hf.2.comp_isClosedEmbedding (isClosedEmbedding_prodMkLeft y)⟩

end Last
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

private inductive RootIndex
  | left12
  | left23
  | left13
  | right12
  | right23
  | right13

section Families

variable {F : Type*} [Field F]

private def rootCoeff (χ : AddChar F ℂ) : RootIndex × F → ℂ
  | (.left12, s) => χ s
  | (.left23, s) => χ s
  | (.left13, _) => 1
  | (.right12, s) => χ s
  | (.right23, s) => χ s
  | (.right13, _) => 1

variable [TopologicalSpace F] [IsTopologicalRing F]

private def bigCellHomeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F))
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => bigCellRight12Homeomorph s
  | (.right23, s) => bigCellRight23Homeomorph s
  | (.right13, s) => bigCellRight13Homeomorph s

private theorem bigCellHomeo_torus :
    ∀ i : RootIndex × F, ∀ x, (bigCellHomeo i x).2.1 = x.2.1 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact bigCellRight12_torus s x
  · exact bigCellRight23_torus s x
  · exact bigCellRight13_torus s x

private def bigCellOps (χ : AddChar F ℂ) (i : RootIndex × F) :
    FibrewiseOp ((F × F × F) × (F × F × F)) (Fˣ × Fˣ × Fˣ) :=
  opOfMapMid (rootCoeff χ i) (bigCellHomeo i)

private def cycle123Homeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F))
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => cycle123Right12Homeomorph s
  | (.right23, s) => cycle123Right23Homeomorph s
  | (.right13, s) => cycle123Right13Homeomorph s

private theorem cycle123Homeo_torus :
    ∀ i : RootIndex × F, ∀ x, (cycle123Homeo i x).2.1 = x.2.1 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact cycle123Right12_torus s x
  · exact cycle123Right23_torus s x
  · exact cycle123Right13_torus s x

private def cycle123Ops (χ : AddChar F ℂ) (i : RootIndex × F) :
    FibrewiseOp ((F × F × F) × (F × F)) (Fˣ × Fˣ × Fˣ) :=
  opOfMapMid (rootCoeff χ i) (cycle123Homeo i)

private def cycle132Homeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F))
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => cycle132Right12Homeomorph s
  | (.right23, s) => cycle132Right23Homeomorph s
  | (.right13, s) => cycle132Right13Homeomorph s

private theorem cycle132Homeo_torus :
    ∀ i : RootIndex × F, ∀ x, (cycle132Homeo i x).2.1 = x.2.1 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact cycle132Right12_torus s x
  · exact cycle132Right23_torus s x
  · exact cycle132Right13_torus s x

private def cycle132Ops (χ : AddChar F ℂ) (i : RootIndex × F) :
    FibrewiseOp ((F × F × F) × (F × F)) (Fˣ × Fˣ × Fˣ) :=
  opOfMapMid (rootCoeff χ i) (cycle132Homeo i)

private def refl12Homeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F)
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => refl12Right12Homeomorph s
  | (.right23, s) => refl12Right23Homeomorph s
  | (.right13, s) => refl12Right13Homeomorph s

private theorem refl12Homeo_torus :
    ∀ i : RootIndex × F, ∀ x, (refl12Homeo i x).2.1 = x.2.1 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact refl12Right12_torus s x
  · exact refl12Right23_torus s x
  · exact refl12Right13_torus s x

private def refl12Ops (χ : AddChar F ℂ) (i : RootIndex × F) :
    FibrewiseOp ((F × F × F) × F) (Fˣ × Fˣ × Fˣ) :=
  opOfMapMid (rootCoeff χ i) (refl12Homeo i)

private def refl23Homeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F)
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => refl23Right12Homeomorph s
  | (.right23, s) => refl23Right23Homeomorph s
  | (.right13, s) => refl23Right13Homeomorph s

private theorem refl23Homeo_torus :
    ∀ i : RootIndex × F, ∀ x, (refl23Homeo i x).2.1 = x.2.1 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact refl23Right12_torus s x
  · exact refl23Right23_torus s x
  · exact refl23Right13_torus s x

private def refl23Ops (χ : AddChar F ℂ) (i : RootIndex × F) :
    FibrewiseOp ((F × F × F) × F) (Fˣ × Fˣ × Fˣ) :=
  opOfMapMid (rootCoeff χ i) (refl23Homeo i)

private def borelHomeo : RootIndex × F →
    ((F × F × F) × (Fˣ × Fˣ × Fˣ)) ≃ₜ ((F × F × F) × (Fˣ × Fˣ × Fˣ))
  | (.left12, s) => (leftRoot12Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left23, s) => (leftRoot23Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.left13, s) => (leftRoot13Homeomorph s).prodCongr (Homeomorph.refl _)
  | (.right12, s) => borelRight12Homeomorph s
  | (.right23, s) => borelRight23Homeomorph s
  | (.right13, s) => borelRight13Homeomorph s

private theorem borelHomeo_torus : ∀ i : RootIndex × F, ∀ x, (borelHomeo i x).2 = x.2 := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ x
  · rfl
  · rfl
  · rfl
  · exact borelRight12_torus s x
  · exact borelRight23_torus s x
  · exact borelRight13_torus s x

private def borelOps (χ : AddChar F ℂ) (i : RootIndex × F) : FibrewiseOp (F × F × F) (Fˣ × Fˣ × Fˣ) :=
  opOfMapLast (rootCoeff χ i) (borelHomeo i)

end Families
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatIntegral LanglandsTunnell.TateLocal

namespace WhittakerCoinvariantsGL3

section Mismatch

variable {K : Type*}

private theorem mem_of_coeff_ne {M : Submodule ℂ (K → ℂ)} {P : (K → ℂ) → Prop} {S B : K → K} {c₁ c₂ : ℂ}
    (hc : c₁ ≠ c₂) (hPS : ∀ g, P g → P (g ∘ S)) (hS : ∀ g, P g → g ∘ S - g ∈ M)
    (h₁ : ∀ g, P g → c₁ • ((g ∘ S) ∘ B) - g ∈ M) (h₂ : ∀ g, P g → c₂ • (g ∘ B) - g ∈ M)
    {g : K → ℂ} (hg : P g) : g ∈ M := by
  have e0 : g ∘ S - g ∈ M := hS g hg
  have e1 : c₁ • ((g ∘ S) ∘ B) - g ∈ M := h₁ g hg
  have e2 : c₂ • ((g ∘ S) ∘ B) - g ∘ S ∈ M := h₂ (g ∘ S) (hPS g hg)
  have key : (c₂ - c₁) • g = c₁ • (c₂ • ((g ∘ S) ∘ B) - g ∘ S) - c₂ • (c₁ • ((g ∘ S) ∘ B) - g)
      + c₁ • (g ∘ S - g) := by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hmem : (c₂ - c₁) • g ∈ M := by
    rw [key]
    exact M.add_mem (M.sub_mem (M.smul_mem c₁ e2) (M.smul_mem c₂ e1)) (M.smul_mem c₁ e0)
  have hne : c₂ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have h := M.smul_mem (c₂ - c₁)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h

end Mismatch
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section FibreShears

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def cShift (v : F) : ((F × F × F) × F) ≃ₜ ((F × F × F) × F) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + v), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - v), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def cShear {e : (F × F) × F → F} (he : Continuous e) : ((F × F × F) × F) ≃ₜ ((F × F × F) × F) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + e ((k.1.1, k.1.2.1), k.2)), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - e ((k.1.1, k.1.2.1), k.2)), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem comp_cShear_sub_mem [T2Space F] (hF : HasClopenBasis F)
    {M : Submodule ℂ ((F × F × F) × F → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × F → ℂ, IsSchwartzBruhat f → f ∘ (cShift v) - f ∈ M)
    {e : (F × F) × F → F} (he : Continuous e) {g : (F × F × F) × F → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (cShear he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F) × F) := (hF.prod hF).prod hF
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × F) hY
    (φ := fun k : (F × F × F) × F => ((k.1.1, k.1.2.1), k.2)) (by fun_prop) (fun v : F => cShift v)
    (fun v k => rfl) (cShear he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (cShift v))
      (sbSubmodule ((F × F × F) × F)) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

end FibreShears
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Refl12

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private theorem refl12_mem_fibreSpan [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ) {u : F}
    (hu : χ u ≠ 1) (t : Fˣ × Fˣ × Fˣ) {g : (F × F × F) × F → ℂ} (hg : IsSchwartzBruhat g) :
    g ∈ fibreSpan (refl12Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have hρ : ((t₂ * t₃⁻¹ : Fˣ) : F) ≠ 0 := (t₂ * t₃⁻¹).ne_zero
  have hsu : u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹ * ((t₂ * t₃⁻¹ : Fˣ) : F) = u := inv_mul_cancel_right₀ hρ u
  have h13 : ∀ v : F, ∀ f : (F × F × F) × F → ℂ, IsSchwartzBruhat f →
      f ∘ (cShift v) - f ∈ fibreSpan (refl12Ops χ) (t₁, t₂, t₃) := by
    intro v f hf
    have h := fibreRelation_mem_fibreSpan (refl12Ops χ) (t₁, t₂, t₃) (RootIndex.left13, v) hf
    have e : (refl12Ops χ (RootIndex.left13, v)).fibreRelation (t₁, t₂, t₃) f =
        f ∘ (cShift v) - f := by
      funext k
      show (1 : ℂ) * f (cShift v k) - f k = f (cShift v k) - f k
      rw [one_mul]
    rw [e] at h
    exact h
  refine mem_of_coeff_ne (M := fibreSpan (refl12Ops χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
    (S := cShear (e := fun y : (F × F) × F =>
      y.1.1 * (u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹) * ((t₂ * t₃⁻¹ : Fˣ) : F)) (by fun_prop))
    (B := fun k : (F × F × F) × F =>
      ((k.1.1, k.1.2.1 + u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹ * ((t₂ * t₃⁻¹ : Fˣ) : F), k.1.2.2), k.2))
    (c₁ := 1) (c₂ := χ (u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹ * ((t₂ * t₃⁻¹ : Fˣ) : F))) ?_ ?_ ?_ ?_ ?_ hg
  · rw [hsu]
    exact hu.symm
  · intro g hg
    exact isSchwartzBruhat_comp_homeo hg _
  · intro g hg
    exact comp_cShear_sub_mem hF h13 _ hg
  · intro g hg
    exact fibreRelation_mem_fibreSpan (refl12Ops χ) (t₁, t₂, t₃)
      (RootIndex.right13, u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹) hg
  · intro g hg
    exact fibreRelation_mem_fibreSpan (refl12Ops χ) (t₁, t₂, t₃)
      (RootIndex.left23, u * ((t₂ * t₃⁻¹ : Fˣ) : F)⁻¹ * ((t₂ * t₃⁻¹ : Fˣ) : F)) hg

private theorem refl12_apply_eq_zero [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : χ ≠ 1)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F),
      T ((refl12Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hχ
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (refl12Ops χ i).toLinMid)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F => x.2.1) (fun i => (refl12Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (refl12Homeo i) (refl12Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (refl12Homeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (refl12Ops χ) hV hVc ht
      (refl12_mem_fibreSpan hF χ hu t (isSchwartzBruhat_fibreMid hf t))

end Refl12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Refl23

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private theorem refl23_mem_fibreSpan [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ) {u : F}
    (hu : χ u ≠ 1) (t : Fˣ × Fˣ × Fˣ) {g : (F × F × F) × F → ℂ} (hg : IsSchwartzBruhat g) :
    g ∈ fibreSpan (refl23Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have hρ : ((t₁ * t₂⁻¹ : Fˣ) : F) ≠ 0 := (t₁ * t₂⁻¹).ne_zero
  have hsu : u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F) = u := inv_mul_cancel_right₀ hρ u
  have h13 : ∀ v : F, ∀ f : (F × F × F) × F → ℂ, IsSchwartzBruhat f →
      f ∘ (cShift v) - f ∈ fibreSpan (refl23Ops χ) (t₁, t₂, t₃) := by
    intro v f hf
    have h := fibreRelation_mem_fibreSpan (refl23Ops χ) (t₁, t₂, t₃) (RootIndex.left13, v) hf
    have e : (refl23Ops χ (RootIndex.left13, v)).fibreRelation (t₁, t₂, t₃) f =
        f ∘ (cShift v) - f := by
      funext k
      show (1 : ℂ) * f (cShift v k) - f k = f (cShift v k) - f k
      rw [one_mul]
    rw [e] at h
    exact h
  refine mem_of_coeff_ne (M := fibreSpan (refl23Ops χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
    (S := cShear (e := fun y : (F × F) × F =>
      y.1.2 * (u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F))) (by fun_prop))
    (B := fun k : (F × F × F) × F =>
      ((k.1.1 + u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F), k.1.2.1, k.1.2.2), k.2))
    (c₁ := χ (u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F))) (c₂ := 1) ?_ ?_ ?_ ?_ ?_ hg
  · rw [hsu]
    exact hu
  · intro g hg
    exact isSchwartzBruhat_comp_homeo hg _
  · intro g hg
    exact comp_cShear_sub_mem hF h13 _ hg
  · intro g hg
    exact fibreRelation_mem_fibreSpan (refl23Ops χ) (t₁, t₂, t₃)
      (RootIndex.left12, u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F)) hg
  · intro g hg
    have h := fibreRelation_mem_fibreSpan (refl23Ops χ) (t₁, t₂, t₃)
      (RootIndex.right13, u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹) hg
    have e :
        (refl23Ops χ (RootIndex.right13, u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹)).fibreRelation (t₁, t₂, t₃) g =
        (1 : ℂ) • (g ∘ fun k : (F × F × F) × F =>
          ((k.1.1 + u * ((t₁ * t₂⁻¹ : Fˣ) : F)⁻¹ * ((t₁ * t₂⁻¹ : Fˣ) : F), k.1.2.1, k.1.2.2),
            k.2)) - g := by
      funext k
      rfl
    rw [e] at h
    exact h

private theorem refl23_apply_eq_zero [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : χ ≠ 1)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × F),
      T ((refl23Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hχ
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (refl23Ops χ i).toLinMid)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F => x.2.1) (fun i => (refl23Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (refl23Homeo i) (refl23Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (refl23Homeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (refl23Ops χ) hV hVc ht
      (refl23_mem_fibreSpan hF χ hu t (isSchwartzBruhat_fibreMid hf t))

end Refl23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

section

noncomputable section

open SchwartzBruhatIntegral LanglandsTunnell.TateLocal

namespace WhittakerCoinvariantsGL3

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

section FibreShears3

private def shift3 (v : F) : (F × F × F) ≃ₜ (F × F × F) where
  toFun k := (k.1, k.2.1, k.2.2 + v)
  invFun k := (k.1, k.2.1, k.2.2 - v)
  left_inv k := by
    obtain ⟨a, b, c⟩ := k
    simp
  right_inv k := by
    obtain ⟨a, b, c⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def shear3 {e : F × F → F} (he : Continuous e) : (F × F × F) ≃ₜ (F × F × F) where
  toFun k := (k.1, k.2.1, k.2.2 + e (k.1, k.2.1))
  invFun k := (k.1, k.2.1, k.2.2 - e (k.1, k.2.1))
  left_inv k := by
    obtain ⟨a, b, c⟩ := k
    simp
  right_inv k := by
    obtain ⟨a, b, c⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem comp_shear3_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ (F × F × F → ℂ)}
    (h13 : ∀ v : F, ∀ f : F × F × F → ℂ, IsSchwartzBruhat f → f ∘ (shift3 v) - f ∈ M)
    {e : F × F → F} (he : Continuous e) {g : F × F × F → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (shear3 he) - g ∈ M := by
  have hY : HasClopenBasis (F × F) := hF.prod hF
  have hmem := comp_shear_sub_mem_coinvariants (X := F × F × F) hY
    (φ := fun k : F × F × F => (k.1, k.2.1)) (by fun_prop) (fun v : F => shift3 v)
    (fun v k => rfl) (shear3 he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (shift3 v))
      (sbSubmodule (F × F × F)) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

end FibreShears3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section FibreData

private def borelChar (χ : AddChar F ℂ) : AddChar (F × F × F) ℂ where
  toFun k := χ k.1 * χ k.2.1
  map_zero_eq_one' := by
    simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem borelChar_apply (χ : AddChar F ℂ) (k : F × F × F) : borelChar χ k = χ k.1 * χ k.2.1 :=
  rfl

private def swapAB : (F × F × F) ≃+ (F × F × F) where
  toFun k := (k.2.1, k.1, k.2.2)
  invFun k := (k.2.1, k.1, k.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem swapAB_apply (k : F × F × F) : swapAB k = (k.2.1, k.1, k.2.2) :=
  rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem swapAB_symm_apply (k : F × F × F) : swapAB.symm k = (k.2.1, k.1, k.2.2) :=
  rfl

omit [IsTopologicalRing F] in
private theorem continuous_swapAB : Continuous (swapAB : F × F × F → F × F × F) := by
  show Continuous fun k : F × F × F => (k.2.1, k.1, k.2.2)
  fun_prop

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem borelChar_comp_swapAB (χ : AddChar F ℂ) :
    (borelChar χ).compAddMonoidHom (swapAB (F := F)).symm.toAddMonoidHom = borelChar χ := by
  refine AddChar.ext _ _ fun k => ?_
  obtain ⟨a, b, c⟩ := k
  show χ b * χ a = χ a * χ b
  exact mul_comm _ _

omit [IsTopologicalRing F] in
private theorem isLocallyConstant_borelChar (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x) :
    IsLocallyConstant fun k : F × F × F => borelChar χ k :=
  (hχ.comp_continuous continuous_fst).mul (hχ.comp_continuous (continuous_fst.comp continuous_snd))

end FibreData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Fibres

private theorem borel_mem_fibreSpan_of_not [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ) {u : F}
    (hu : χ u ≠ 1) {t₁ t₂ t₃ : Fˣ} (hne : ¬ (t₁ = t₂ ∧ t₂ = t₃)) {g : F × F × F → ℂ}
    (hg : IsSchwartzBruhat g) : g ∈ fibreSpan (borelOps χ) (t₁, t₂, t₃) := by
  have h13 : ∀ v : F, ∀ f : F × F × F → ℂ, IsSchwartzBruhat f →
      f ∘ (shift3 v) - f ∈ fibreSpan (borelOps χ) (t₁, t₂, t₃) := by
    intro v f hf
    have h := fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₂, t₃) (RootIndex.left13, v) hf
    have e : (borelOps χ (RootIndex.left13, v)).fibreRelation (t₁, t₂, t₃) f =
        f ∘ (shift3 v) - f := by
      funext k
      show (1 : ℂ) * f (shift3 v k) - f k = f (shift3 v k) - f k
      rw [one_mul]
    rw [e] at h
    exact h
  have hχne : ∀ s w : F, s = w + u → χ w ≠ χ s := by
    rintro s w rfl h
    rw [AddChar.map_add_eq_mul] at h
    exact hu (mul_left_cancel₀ (addChar_ne_zero χ w) (h.symm.trans (mul_one _).symm))
  by_cases h12 : ((t₁ * t₂⁻¹ : Fˣ) : F) = 1
  ·
    have h12' : t₁ = t₂ := mul_inv_eq_one.mp (Units.val_eq_one.mp h12)
    set ρ : F := ((t₂ * t₃⁻¹ : Fˣ) : F) with hρdef
    have h23 : ρ ≠ 1 := fun h => hne ⟨h12', mul_inv_eq_one.mp (Units.val_eq_one.mp h)⟩
    have hρ : ρ - 1 ≠ 0 := sub_ne_zero.mpr h23
    have hs : u * (ρ - 1)⁻¹ * ρ = u * (ρ - 1)⁻¹ + u := by
      have h := inv_mul_cancel_right₀ hρ u
      linear_combination h
    refine mem_of_coeff_ne (M := fibreSpan (borelOps χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
      (S := shear3 (e := fun y : F × F => y.1 * (u * (ρ - 1)⁻¹) * ρ) (by fun_prop))
      (B := fun k : F × F × F => (k.1, k.2.1 + u * (ρ - 1)⁻¹ * ρ, k.2.2))
      (c₁ := χ (u * (ρ - 1)⁻¹)) (c₂ := χ (u * (ρ - 1)⁻¹ * ρ)) ?_ ?_ ?_ ?_ ?_ hg
    · exact hχne _ _ hs
    · intro g hg
      exact isSchwartzBruhat_comp_homeo hg _
    · intro g hg
      exact comp_shear3_sub_mem hF h13 _ hg
    · intro g hg
      exact fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₂, t₃)
        (RootIndex.right23, u * (ρ - 1)⁻¹) hg
    · intro g hg
      exact fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₂, t₃)
        (RootIndex.left23, u * (ρ - 1)⁻¹ * ρ) hg
  ·
    set ρ : F := ((t₁ * t₂⁻¹ : Fˣ) : F) with hρdef
    have hρ : ρ - 1 ≠ 0 := sub_ne_zero.mpr h12
    have hs : u * (ρ - 1)⁻¹ * ρ = u * (ρ - 1)⁻¹ + u := by
      have h := inv_mul_cancel_right₀ hρ u
      linear_combination h
    refine mem_of_coeff_ne (M := fibreSpan (borelOps χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
      (S := shear3 (e := fun y : F × F => y.2 * (u * (ρ - 1)⁻¹ * ρ)) (by fun_prop))
      (B := fun k : F × F × F => (k.1 + u * (ρ - 1)⁻¹ * ρ, k.2.1, k.2.2))
      (c₁ := χ (u * (ρ - 1)⁻¹ * ρ)) (c₂ := χ (u * (ρ - 1)⁻¹)) ?_ ?_ ?_ ?_ ?_ hg
    · exact (hχne _ _ hs).symm
    · intro g hg
      exact isSchwartzBruhat_comp_homeo hg _
    · intro g hg
      exact comp_shear3_sub_mem hF h13 _ hg
    · intro g hg
      exact fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₂, t₃)
        (RootIndex.left12, u * (ρ - 1)⁻¹ * ρ) hg
    · intro g hg
      exact fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₂, t₃)
        (RootIndex.right12, u * (ρ - 1)⁻¹) hg

private theorem twistedSpan_borelChar_le (χ : AddChar F ℂ) (t₁ : Fˣ) :
    twistedSpan (borelChar χ) ≤ fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
  have hρ : ((t₁ * t₁⁻¹ : Fˣ) : F) = 1 := by
    rw [mul_inv_cancel, Units.val_one]
  have hA : ∀ s : F, ∀ g : F × F × F → ℂ, IsSchwartzBruhat g →
      twistedRel (borelChar χ) ((s, 0, 0) : F × F × F) g ∈ fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
    intro s g hg
    have r := fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₁, t₁) (RootIndex.right12, s) hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have e : twistedRel (borelChar χ) ((s, 0, 0) : F × F × F) g =
        (χ s)⁻¹ • (borelOps χ (RootIndex.right12, s)).fibreRelation (t₁, t₁, t₁) g := by
      funext k
      obtain ⟨a, b, c⟩ := k
      show g ((a, b, c) + (s, 0, 0)) - (borelChar χ (s, 0, 0))⁻¹ * g (a, b, c) =
        (χ s)⁻¹ * (χ s * g (a + s * ((t₁ * t₁⁻¹ : Fˣ) : F), b, c) - g (a, b, c))
      rw [borelChar_apply]
      simp only [Prod.mk_add_mk, add_zero, AddChar.map_zero_eq_one, mul_one, hρ]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r
  have hB : ∀ s : F, ∀ g : F × F × F → ℂ, IsSchwartzBruhat g →
      twistedRel (borelChar χ) ((0, s, 0) : F × F × F) g ∈ fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
    intro s g hg
    have r := fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₁, t₁) (RootIndex.left23, s) hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have e : twistedRel (borelChar χ) ((0, s, 0) : F × F × F) g =
        (χ s)⁻¹ • (borelOps χ (RootIndex.left23, s)).fibreRelation (t₁, t₁, t₁) g := by
      funext k
      obtain ⟨a, b, c⟩ := k
      show g ((a, b, c) + (0, s, 0)) - (borelChar χ (0, s, 0))⁻¹ * g (a, b, c) =
        (χ s)⁻¹ * (χ s * g (a, b + s, c) - g (a, b, c))
      rw [borelChar_apply]
      simp only [Prod.mk_add_mk, add_zero, AddChar.map_zero_eq_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r
  have hC : ∀ s : F, ∀ g : F × F × F → ℂ, IsSchwartzBruhat g →
      twistedRel (borelChar χ) ((0, 0, s) : F × F × F) g ∈ fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
    intro s g hg
    have r := fibreRelation_mem_fibreSpan (borelOps χ) (t₁, t₁, t₁) (RootIndex.left13, s) hg
    have e : twistedRel (borelChar χ) ((0, 0, s) : F × F × F) g =
        (borelOps χ (RootIndex.left13, s)).fibreRelation (t₁, t₁, t₁) g := by
      funext k
      obtain ⟨a, b, c⟩ := k
      show g ((a, b, c) + (0, 0, s)) - (borelChar χ (0, 0, s))⁻¹ * g (a, b, c) =
        1 * g (a, b, c + s) - g (a, b, c)
      rw [borelChar_apply]
      simp only [Prod.mk_add_mk, add_zero, AddChar.map_zero_eq_one, mul_one, inv_one, one_mul]
    rw [e]
    exact r
  refine twistedSpan_le_of_axes (borelChar χ) (fun s g hg => hA s g hg) ?_
  intro bc g hg
  have hx : ((0, bc.1, 0) : F × F × F) ∈ relationClosed (borelChar χ)
      (fibreSpan (borelOps χ) (t₁, t₁, t₁)) :=
    (mem_relationClosed_iff _ _ _).mpr fun g hg => hB bc.1 g hg
  have hy : ((0, 0, bc.2) : F × F × F) ∈ relationClosed (borelChar χ)
      (fibreSpan (borelOps χ) (t₁, t₁, t₁)) :=
    (mem_relationClosed_iff _ _ _).mpr fun g hg => hC bc.2 g hg
  have hsum : ((0 : F), bc) = ((0, bc.1, 0) : F × F × F) + (0, 0, bc.2) := by
    obtain ⟨b, c⟩ := bc
    ext <;> simp
  rw [hsum]
  exact (mem_relationClosed_iff _ _ _).mp ((relationClosed _ _).add_mem hx hy) g hg

private theorem sub_comp_swapAB_mem_fibreSpan (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData (F × F × F)) (hc : IsCompact (D.ref : Set (F × F × F)))
    (hκ : D.IsAdmissibleAut swapAB) (t₁ : Fˣ) {g : F × F × F → ℂ} (hg : IsSchwartzBruhat g) :
    g - (fun k => g (swapAB k)) ∈ fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
  have hχK := isLocallyConstant_borelChar χ hχ
  have hgs : IsSchwartzBruhat fun k => g (swapAB k) := isSchwartzBruhat_comp_homeo hg hκ.homeo
  have hcomp : D.twistedIntegral (borelChar χ) (fun k => g (swapAB k)) =
      D.twistedIntegral (borelChar χ) g := by
    rw [D.twistedIntegral_comp (borelChar χ) hκ hχK hg, borelChar_comp_swapAB]
  have h0 : D.twistedIntegral (borelChar χ) (g - fun k => g (swapAB k)) = 0 := by
    have h1 : (g - fun k => g (swapAB k)) = g - (1 : ℂ) • fun k => g (swapAB k) := by
      rw [one_smul]
    rw [h1, D.twistedIntegral_sub_smul (borelChar χ) hχK hg hgs 1, hcomp]
    ring
  have hsub : IsSchwartzBruhat (g - fun k => g (swapAB k)) :=
    mem_sbSubmodule.mp ((sbSubmodule _).sub_mem (mem_sbSubmodule.mpr hg) (mem_sbSubmodule.mpr hgs))
  exact D.mem_of_twistedIntegral_eq_zero (borelChar χ) hc hχK (twistedSpan_borelChar_le χ t₁) hsub h0

private theorem borel_fibre_sub_mem_of_eq [T2Space F] (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData (F × F × F))
    (hc : IsCompact (D.ref : Set (F × F × F))) (hκ : D.IsAdmissibleAut swapAB) (t₁ : Fˣ)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) → ℂ} (hf : IsSchwartzBruhat f) :
    (fun k => (f - compLin borelInvolutionHomeomorph f) (k, (t₁, t₁, t₁))) ∈
      fibreSpan (borelOps χ) (t₁, t₁, t₁) := by
  have e : (fun k => (f - compLin borelInvolutionHomeomorph f) (k, (t₁, t₁, t₁))) =
      (fun k => f (k, (t₁, t₁, t₁))) - fun k => (fun k => f (k, (t₁, t₁, t₁))) (swapAB k) := by
    funext k
    obtain ⟨a, b, c⟩ := k
    show f ((a, b, c), (t₁, t₁, t₁)) - f (borelInvolution ((a, b, c), (t₁, t₁, t₁))) =
      f ((a, b, c), (t₁, t₁, t₁)) - f ((b, a, c), (t₁, t₁, t₁))
    rw [borelInvolution_of_eq a b c t₁ t₁ t₁ rfl rfl]
  rw [e]
  exact sub_comp_swapAB_mem_fibreSpan χ hχ D hc hκ t₁ (isSchwartzBruhat_fibreLast hf _)

end Fibres
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Main

private theorem borel_apply_comp_involution_eq [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData (F × F × F)) (hc : IsCompact (D.ref : Set (F × F × F)))
    (hκ : D.IsAdmissibleAut swapAB)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ)),
      T ((borelOps χ i).toLin f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) → ℂ} (hf : IsSchwartzBruhat f) :
    T (f ∘ borelInvolutionHomeomorph) = T f := by
  obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hχ1
  have hΘS : ∀ g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ)),
      compLin borelInvolutionHomeomorph g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ)) :=
    fun g hg => mem_sbSubmodule.mpr (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hg) _)
  refine Localisation.apply_eq_of_forall_fibre Prod.snd (fun i => (borelOps χ i).toLin)
    (sbSubmodule _) continuous_snd hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (compLin borelInvolutionHomeomorph) hΘS ?_ T hT
    (mem_sbSubmodule.mpr hf)
  · intro g hg V hV
    exact indicator_preimage_mem continuous_snd (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLin_opOfMapLast_mem (rootCoeff χ i) (borelHomeo i) (borelHomeo_torus i) g hg
  · intro i V _ g _
    exact toLin_opOfMapLast_indicator (rootCoeff χ i) (borelHomeo_torus i) V g
  · intro g hg y _
    obtain ⟨t₁, t₂, t₃⟩ := y
    obtain ⟨V, hV, hVc, hy⟩ := hYc (t₁, t₂, t₃)
    refine exists_mem_coinvariants_forall_snd_eq (borelOps χ) hV hVc hy ?_
    by_cases hrel : t₁ = t₂ ∧ t₂ = t₃
    · obtain ⟨h12, h23⟩ := hrel
      subst h23
      subst h12
      exact borel_fibre_sub_mem_of_eq χ hχ D hc hκ t₁ (mem_sbSubmodule.mp hg)
    · exact borel_mem_fibreSpan_of_not hF χ hu hrel
        (isSchwartzBruhat_fibreLast (mem_sbSubmodule.mp ((sbSubmodule _).sub_mem hg (hΘS g hg))) _)

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

noncomputable section

open SchwartzBruhatIntegral LanglandsTunnell.TateLocal

namespace WhittakerCoinvariantsGL3

section Algebra

variable {K : Type*}

private theorem smul_comp_sub_mem_of_bridge {M : Submodule ℂ (K → ℂ)} {g : K → ℂ} {B S : K → K} {c : ℂ}
    (h₁ : c • ((g ∘ B) ∘ S) - g ∈ M) (hS : (g ∘ B) ∘ S - g ∘ B ∈ M) : c • (g ∘ B) - g ∈ M := by
  have key : c • (g ∘ B) - g = (c • ((g ∘ B) ∘ S) - g) - c • ((g ∘ B) ∘ S - g ∘ B) := by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply]
    ring
  rw [key]
  exact M.sub_mem h₁ (M.smul_mem c hS)

private theorem comp_trans_sub_mem [TopologicalSpace K] {M : Submodule ℂ (K → ℂ)} {g : K → ℂ}
    (e₁ e₂ : K ≃ₜ K) (h₁ : (g ∘ e₂) ∘ e₁ - g ∘ e₂ ∈ M) (h₂ : g ∘ e₂ - g ∈ M) :
    g ∘ (e₁.trans e₂) - g ∈ M := by
  have h := M.add_mem h₁ h₂
  rw [sub_add_sub_cancel] at h
  exact h

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Character

variable {F : Type*} [Field F]

private theorem addChar_apply_ne_of_eq_add [TopologicalSpace F] (χ : AddChar F ℂ) {u : F} (hu : χ u ≠ 1)
    {s w : F} (h : s = w + u) : χ w ≠ χ s := by
  subst h
  intro h
  rw [AddChar.map_add_eq_mul] at h
  exact hu (mul_left_cancel₀ (addChar_ne_zero χ w) (h.symm.trans (mul_one _).symm))

private theorem rescale_mul_eq_add (u : F) {ρ : F} (hρ : ρ - 1 ≠ 0) :
    u * (ρ - 1)⁻¹ * ρ = u * (ρ - 1)⁻¹ + u := by
  have h := inv_mul_cancel_right₀ hρ u
  linear_combination h

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section FibreMaps

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def aTrans (v : F) : ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := ((k.1.1 + v, k.1.2.1, k.1.2.2), k.2)
  invFun k := ((k.1.1 - v, k.1.2.1, k.1.2.2), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def cTrans (v : F) : ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + v), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - v), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rTrans (v : F) : ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2 + v))
  invFun k := (k.1, (k.2.1, k.2.2 - v))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def cShearAdd {e : (F × F) × (F × F) → F} (he : Continuous e) :
    ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + e ((k.1.1, k.1.2.1), k.2)), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - e ((k.1.1, k.1.2.1), k.2)), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def cShearSub {e : (F × F) × (F × F) → F} (he : Continuous e) :
    ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 - e ((k.1.1, k.1.2.1), k.2)), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 + e ((k.1.1, k.1.2.1), k.2)), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rShearAdd {e : (F × F × F) × F → F} (he : Continuous e) :
    ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2 + e (k.1, k.2.1)))
  invFun k := (k.1, (k.2.1, k.2.2 - e (k.1, k.2.1)))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rShearSub {e : (F × F × F) × F → F} (he : Continuous e) :
    ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2 - e (k.1, k.2.1)))
  invFun k := (k.1, (k.2.1, k.2.2 + e (k.1, k.2.1)))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rShearAddLeft {e : (F × F × F) × F → F} (he : Continuous e) :
    ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) where
  toFun k := (k.1, (k.2.1, e (k.1, k.2.1) + k.2.2))
  invFun k := (k.1, (k.2.1, k.2.2 - e (k.1, k.2.1)))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private
theorem comp_cShearAdd_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat f → f ∘ (cTrans v) - f ∈ M)
    {e : (F × F) × (F × F) → F} (he : Continuous e) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (cShearAdd he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F) × (F × F)) := (hF.prod hF).prod (hF.prod hF)
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F)) hY
    (φ := fun k : (F × F × F) × (F × F) => ((k.1.1, k.1.2.1), k.2)) (by fun_prop) (fun v : F => cTrans v)
    (fun v k => rfl) (cShearAdd he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (cTrans v))
      (sbSubmodule ((F × F × F) × (F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

private
theorem comp_cShearSub_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat f → f ∘ (cTrans v) - f ∈ M)
    {e : (F × F) × (F × F) → F} (he : Continuous e) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (cShearSub he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F) × (F × F)) := (hF.prod hF).prod (hF.prod hF)
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F)) hY
    (φ := fun k : (F × F × F) × (F × F) => ((k.1.1, k.1.2.1), k.2)) (by fun_prop) (fun v : F => cTrans v)
    (fun v k => rfl) (cShearSub he) (c := fun y => -e y)
    (fun k => Prod.ext (Prod.ext rfl (Prod.ext rfl (sub_eq_add_neg _ _))) rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (cTrans v))
      (sbSubmodule ((F × F × F) × (F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

private
theorem comp_rShearAdd_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat f → f ∘ (rTrans v) - f ∈ M)
    {e : (F × F × F) × F → F} (he : Continuous e) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (rShearAdd he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F × F) × F) := (hF.prod (hF.prod hF)).prod hF
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F)) hY
    (φ := fun k : (F × F × F) × (F × F) => (k.1, k.2.1)) (by fun_prop) (fun v : F => rTrans v)
    (fun v k => rfl) (rShearAdd he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (rTrans v))
      (sbSubmodule ((F × F × F) × (F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

private
theorem comp_rShearSub_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat f → f ∘ (rTrans v) - f ∈ M)
    {e : (F × F × F) × F → F} (he : Continuous e) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (rShearSub he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F × F) × F) := (hF.prod (hF.prod hF)).prod hF
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F)) hY
    (φ := fun k : (F × F × F) × (F × F) => (k.1, k.2.1)) (by fun_prop) (fun v : F => rTrans v)
    (fun v k => rfl) (rShearSub he) (c := fun z => -e z)
    (fun k => Prod.ext rfl (Prod.ext rfl (sub_eq_add_neg _ _))) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (rTrans v))
      (sbSubmodule ((F × F × F) × (F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

private
theorem comp_rShearAddLeft_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat f → f ∘ (rTrans v) - f ∈ M)
    {e : (F × F × F) × F → F} (he : Continuous e) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (rShearAddLeft he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F × F) × F) := (hF.prod (hF.prod hF)).prod hF
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F)) hY
    (φ := fun k : (F × F × F) × (F × F) => (k.1, k.2.1)) (by fun_prop) (fun v : F => rTrans v)
    (fun v k => rfl) (rShearAddLeft he) (c := e)
    (fun k => Prod.ext rfl (Prod.ext rfl (add_comm _ _))) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (rTrans v))
      (sbSubmodule ((F × F × F) × (F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

end FibreMaps
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section FibreData

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def cycleChar (χ : AddChar F ℂ) : AddChar ((F × F × F) × (F × F)) ℂ where
  toFun k := χ k.1.1 * χ k.1.2.1 * χ k.2.1
  map_zero_eq_one' := by
    simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem cycleChar_apply (χ : AddChar F ℂ) (k : (F × F × F) × (F × F)) :
    cycleChar χ k = χ k.1.1 * χ k.1.2.1 * χ k.2.1 :=
  rfl

omit [IsTopologicalRing F] in
private theorem isLocallyConstant_cycleChar (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x) :
    IsLocallyConstant fun k : (F × F × F) × (F × F) => cycleChar χ k :=
  ((hχ.comp_continuous (continuous_fst.comp continuous_fst)).mul
    (hχ.comp_continuous (continuous_fst.comp (continuous_snd.comp continuous_fst)))).mul
    (hχ.comp_continuous (continuous_fst.comp continuous_snd))

private def perm123 : ((F × F × F) × (F × F)) ≃+ ((F × F × F) × (F × F)) where
  toFun k := ((k.2.1, k.1.2.1, k.2.2), (k.1.1, k.1.2.2))
  invFun k := ((k.2.1, k.1.2.1, k.2.2), (k.1.1, k.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def perm132 : ((F × F × F) × (F × F)) ≃+ ((F × F × F) × (F × F)) where
  toFun k := ((k.1.1, k.2.1, k.2.2), (k.1.2.1, k.1.2.2))
  invFun k := ((k.1.1, k.2.1, k.2.2), (k.1.2.1, k.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem cycleChar_comp_perm123 (χ : AddChar F ℂ) :
    (cycleChar χ).compAddMonoidHom (perm123 (F := F)).symm.toAddMonoidHom = cycleChar χ := by
  refine AddChar.ext _ _ fun k => ?_
  obtain ⟨⟨a, b, c⟩, q, r⟩ := k
  show χ q * χ b * χ a = χ a * χ b * χ q
  ring

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem cycleChar_comp_perm132 (χ : AddChar F ℂ) :
    (cycleChar χ).compAddMonoidHom (perm132 (F := F)).symm.toAddMonoidHom = cycleChar χ := by
  refine AddChar.ext _ _ fun k => ?_
  obtain ⟨⟨a, b, c⟩, p, r⟩ := k
  show χ a * χ p * χ b = χ a * χ b * χ p
  ring

private def shear123 : ((F × F × F) × (F × F)) ≃ₜ ((F × F × F) × (F × F)) :=
  (cShearSub (e := fun y : (F × F) × (F × F) => y.1.1 * y.1.2) (by fun_prop)).trans
    (rShearAddLeft (e := fun z : (F × F × F) × F => z.1.2.1 * z.2) (by fun_prop))

private theorem twistedSpan_cycleChar_le_of_axes (χ : AddChar F ℂ) {M : Submodule ℂ ((F × F × F) × (F × F) → ℂ)}
    (hA : ∀ s : F, ∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) ((s, 0, 0), 0) g ∈ M)
    (hB : ∀ s : F, ∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) ((0, s, 0), 0) g ∈ M)
    (hC : ∀ s : F, ∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) ((0, 0, s), 0) g ∈ M)
    (hQ : ∀ s : F, ∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) (0, (s, 0)) g ∈ M)
    (hR : ∀ s : F, ∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) (0, (0, s)) g ∈ M) :
    twistedSpan (cycleChar χ) ≤ M := by
  have mem : ∀ {x : (F × F × F) × (F × F)},
      (∀ g : (F × F × F) × (F × F) → ℂ, IsSchwartzBruhat g → twistedRel (cycleChar χ) x g ∈ M) →
        x ∈ relationClosed (cycleChar χ) M :=
    fun h => (mem_relationClosed_iff _ _ _).mpr h
  refine twistedSpan_le_of_axes (cycleChar χ) ?_ ?_
  · intro abc g hg
    obtain ⟨a, b, c⟩ := abc
    have hsum : (((a, b, c), 0) : (F × F × F) × (F × F)) = ((a, 0, 0), 0) + ((0, b, 0), 0) + ((0, 0, c), 0) := by
      ext <;> simp
    rw [hsum]
    exact (mem_relationClosed_iff _ _ _).mp ((relationClosed _ _).add_mem
      ((relationClosed _ _).add_mem (mem (hA a)) (mem (hB b))) (mem (hC c))) g hg
  · intro qr g hg
    obtain ⟨q, r⟩ := qr
    have hsum : ((0, (q, r)) : (F × F × F) × (F × F)) = (0, (q, 0)) + (0, (0, r)) := by
      ext <;> simp
    rw [hsum]
    exact (mem_relationClosed_iff _ _ _).mp
      ((relationClosed _ _).add_mem (mem (hQ q)) (mem (hR r))) g hg

end FibreData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Cycle123

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private theorem cycle123_cTrans_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (cTrans v) - f ∈ fibreSpan (cycle123Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have h := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₃) (RootIndex.left13, v) hf
  have e : (cycle123Ops χ (RootIndex.left13, v)).fibreRelation (t₁, t₂, t₃) f =
      f ∘ (cTrans v) - f := by
    funext k
    show (1 : ℂ) * f (cTrans v k) - f k = f (cTrans v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem cycle123_rTrans_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (rTrans v) - f ∈ fibreSpan (cycle123Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have h := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₃) (RootIndex.right13, v) hf
  have e : (cycle123Ops χ (RootIndex.right13, v)).fibreRelation (t₁, t₂, t₃) f =
      f ∘ (rTrans v) - f := by
    funext k
    show (1 : ℂ) * f (rTrans v k) - f k = f (rTrans v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem cycle123_mem_fibreSpan_of_ne [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    {u : F} (hu : χ u ≠ 1) {t₁ t₂ t₃ : Fˣ} (hne : t₂ ≠ t₃) {g : (F × F × F) × (F × F) → ℂ}
    (hg : IsSchwartzBruhat g) : g ∈ fibreSpan (cycle123Ops χ) (t₁, t₂, t₃) := by
  set ρ : F := ((t₂ * t₃⁻¹ : Fˣ) : F) with hρdef
  have hρ1 : ρ ≠ 1 := fun h => hne (mul_inv_eq_one.mp (Units.val_eq_one.mp h))
  have hρ : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hs := rescale_mul_eq_add u hρ
  refine mem_of_coeff_ne (M := fibreSpan (cycle123Ops χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
    (S := (cShearAdd (e := fun y : (F × F) × (F × F) => y.1.1 * (u * (ρ - 1)⁻¹) * ρ)
      (by fun_prop)).trans (rShearSub (e := fun z : (F × F × F) × F => z.2 * (u * (ρ - 1)⁻¹))
      (by fun_prop)))
    (B := fun k : (F × F × F) × (F × F) => ((k.1.1, k.1.2.1 + u * (ρ - 1)⁻¹ * ρ, k.1.2.2), k.2))
    (c₁ := χ (u * (ρ - 1)⁻¹)) (c₂ := χ (u * (ρ - 1)⁻¹ * ρ)) ?_ ?_ ?_ ?_ ?_ hg
  · exact addChar_apply_ne_of_eq_add χ hu hs
  · intro g hg
    exact isSchwartzBruhat_comp_homeo hg _
  · intro g hg
    exact comp_trans_sub_mem _ _
      (comp_cShearAdd_sub_mem hF (cycle123_cTrans_sub_mem χ _) _ (isSchwartzBruhat_comp_homeo hg _))
      (comp_rShearSub_sub_mem hF (cycle123_rTrans_sub_mem χ _) _ hg)
  · intro g hg
    exact fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₃)
      (RootIndex.right12, u * (ρ - 1)⁻¹) hg
  · intro g hg
    exact fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₃)
      (RootIndex.left23, u * (ρ - 1)⁻¹ * ρ) hg

private theorem twistedSpan_cycleChar_le_cycle123 [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t₁ t₂ : Fˣ) : twistedSpan (cycleChar χ) ≤ fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) := by
  refine twistedSpan_cycleChar_le_of_axes χ ?_ ?_ ?_ ?_ ?_
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have h₁ : χ s • ((g ∘ (aTrans s)) ∘ (cShearAdd (e := fun y : (F × F) × (F × F) => y.1.2 * s)
        (by fun_prop))) - g ∈ fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) :=
      fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) (RootIndex.left12, s) hg
    have hpure : χ s • (g ∘ (aTrans s)) - g ∈ fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) :=
      smul_comp_sub_mem_of_bridge h₁ (comp_cShearAdd_sub_mem hF (cycle123_cTrans_sub_mem χ _) _
        (isSchwartzBruhat_comp_homeo hg _))
    have e : twistedRel (cycleChar χ) (((s, 0, 0), 0) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (χ s • (g ∘ (aTrans s)) - g) := by
      funext k
      obtain ⟨⟨a, b, c⟩, q, r⟩ := k
      show g (((a, b, c), (q, r)) + ((s, 0, 0), 0)) - (cycleChar χ ((s, 0, 0), 0))⁻¹ * g ((a, b, c), (q, r))
        = (χ s)⁻¹ * (χ s * g ((a + s, b, c), (q, r)) - g ((a, b, c), (q, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hpure
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) (RootIndex.left23, s) hg
    have e : twistedRel (cycleChar χ) (((0, s, 0), 0) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (cycle123Ops χ (RootIndex.left23, s)).fibreRelation (t₁, t₂, t₂) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, q, r⟩ := k
      show g (((a, b, c), (q, r)) + ((0, s, 0), 0)) - (cycleChar χ ((0, s, 0), 0))⁻¹ * g ((a, b, c), (q, r))
        = (χ s)⁻¹ * (χ s * g ((a, b + s, c), (q, r)) - g ((a, b, c), (q, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  ·
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) (RootIndex.left13, s) hg
    have e : twistedRel (cycleChar χ) (((0, 0, s), 0) : (F × F × F) × (F × F)) g =
        (cycle123Ops χ (RootIndex.left13, s)).fibreRelation (t₁, t₂, t₂) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, q, r⟩ := k
      show g (((a, b, c), (q, r)) + ((0, 0, s), 0)) - (cycleChar χ ((0, 0, s), 0))⁻¹ * g ((a, b, c), (q, r))
        = 1 * g ((a, b, c + s), (q, r)) - g ((a, b, c), (q, r))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) (RootIndex.right23, s) hg
    have e : twistedRel (cycleChar χ) ((0, (s, 0)) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (cycle123Ops χ (RootIndex.right23, s)).fibreRelation (t₁, t₂, t₂) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, q, r⟩ := k
      show g (((a, b, c), (q, r)) + (0, (s, 0))) - (cycleChar χ (0, (s, 0)))⁻¹ * g ((a, b, c), (q, r))
        = (χ s)⁻¹ * (χ s * g ((a, b, c), (q + s, r)) - g ((a, b, c), (q, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  ·
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) (RootIndex.right13, s) hg
    have e : twistedRel (cycleChar χ) ((0, (0, s)) : (F × F × F) × (F × F)) g =
        (cycle123Ops χ (RootIndex.right13, s)).fibreRelation (t₁, t₂, t₂) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, q, r⟩ := k
      show g (((a, b, c), (q, r)) + (0, (0, s))) - (cycleChar χ (0, (0, s)))⁻¹ * g ((a, b, c), (q, r))
        = 1 * g ((a, b, c), (q, r + s)) - g ((a, b, c), (q, r))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁

private theorem sub_comp_perm123_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F)))) (hP : D.IsAdmissibleAut perm123) (t₁ t₂ : Fˣ)
    {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g - (fun k => g (perm123 k)) ∈ fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) := by
  have hχK := isLocallyConstant_cycleChar χ hχ
  have hgs : IsSchwartzBruhat fun k => g (perm123 k) := isSchwartzBruhat_comp_homeo hg hP.homeo
  have hcomp : D.twistedIntegral (cycleChar χ) (fun k => g (perm123 k)) =
      D.twistedIntegral (cycleChar χ) g := by
    rw [D.twistedIntegral_comp (cycleChar χ) hP hχK hg, cycleChar_comp_perm123]
  have h0 : D.twistedIntegral (cycleChar χ) (g - fun k => g (perm123 k)) = 0 := by
    have h1 : (g - fun k => g (perm123 k)) = g - (1 : ℂ) • fun k => g (perm123 k) := by
      rw [one_smul]
    rw [h1, D.twistedIntegral_sub_smul (cycleChar χ) hχK hg hgs 1, hcomp]
    ring
  have hsub : IsSchwartzBruhat (g - fun k => g (perm123 k)) :=
    mem_sbSubmodule.mp ((sbSubmodule _).sub_mem (mem_sbSubmodule.mpr hg) (mem_sbSubmodule.mpr hgs))
  exact D.mem_of_twistedIntegral_eq_zero (cycleChar χ) hc hχK
    (twistedSpan_cycleChar_le_cycle123 hF χ t₁ t₂) hsub h0

private theorem cycle123_fibre_sub_mem_of_eq [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F)))) (hP : D.IsAdmissibleAut perm123) (t₁ t₂ : Fˣ)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    (fun k : (F × F × F) × (F × F) => (f - compLin cycle123InvolutionHomeomorph f) (k.1, ((t₁, t₂, t₂), k.2))) ∈
      fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) := by
  have hG : IsSchwartzBruhat fun k : (F × F × F) × (F × F) => f (k.1, ((t₁, t₂, t₂), k.2)) :=
    isSchwartzBruhat_fibreMid hf _
  have hGP : IsSchwartzBruhat fun k : (F × F × F) × (F × F) => f ((perm123 k).1, ((t₁, t₂, t₂), (perm123 k).2)) :=
    isSchwartzBruhat_comp_homeo hG hP.homeo
  have e : (fun k : (F × F × F) × (F × F) => (f - compLin cycle123InvolutionHomeomorph f) (k.1, ((t₁, t₂, t₂), k.2))) =
      ((fun k : (F × F × F) × (F × F) => f (k.1, ((t₁, t₂, t₂), k.2))) -
        fun k : (F × F × F) × (F × F) => f ((perm123 k).1, ((t₁, t₂, t₂), (perm123 k).2))) +
      ((fun k : (F × F × F) × (F × F) => f ((perm123 k).1, ((t₁, t₂, t₂), (perm123 k).2))) -
        fun k : (F × F × F) × (F × F) => f ((perm123 (shear123 k)).1, ((t₁, t₂, t₂), (perm123 (shear123 k)).2))) := by
    funext k
    obtain ⟨⟨a, b, c⟩, q, r⟩ := k
    show f ((a, b, c), (t₁, t₂, t₂), (q, r)) - f (cycle123Involution ((a, b, c), (t₁, t₂, t₂), (q, r))) =
      f ((a, b, c), (t₁, t₂, t₂), (q, r)) - f ((q, b, r), (t₁, t₂, t₂), (a, c)) +
        (f ((q, b, r), (t₁, t₂, t₂), (a, c)) - f ((q, b, b * q + r), (t₁, t₂, t₂), (a, c - a * b)))
    rw [cycle123Involution_of_eq a b c q r t₁ t₂ t₂ rfl]
    ring
  rw [e]
  refine Submodule.add_mem _ (sub_comp_perm123_mem hF χ hχ D hc hP t₁ t₂ hG) ?_
  have hb : (fun k : (F × F × F) × (F × F) => f ((perm123 k).1, ((t₁, t₂, t₂), (perm123 k).2))) ∘ shear123 -
      (fun k : (F × F × F) × (F × F) => f ((perm123 k).1, ((t₁, t₂, t₂), (perm123 k).2))) ∈
        fibreSpan (cycle123Ops χ) (t₁, t₂, t₂) :=
    comp_trans_sub_mem _ _
      (comp_cShearSub_sub_mem hF (cycle123_cTrans_sub_mem χ _) _ (isSchwartzBruhat_comp_homeo hGP _))
      (comp_rShearAddLeft_sub_mem hF (cycle123_rTrans_sub_mem χ _) _ hGP)
  have hn := Submodule.neg_mem _ hb
  rw [neg_sub] at hn
  exact hn

private theorem cycle123_apply_comp_involution_eq [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F))) (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F))))
    (hP : D.IsAdmissibleAut perm123)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      T ((cycle123Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    T (f ∘ cycle123InvolutionHomeomorph) = T f := by
  obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hχ1
  have hΘS : ∀ g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      compLin cycle123InvolutionHomeomorph g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :=
    fun g hg => mem_sbSubmodule.mpr (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hg) _)
  refine Localisation.apply_eq_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1) (fun i => (cycle123Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (compLin cycle123InvolutionHomeomorph) hΘS ?_ T
    hT (mem_sbSubmodule.mpr hf)
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (cycle123Homeo i) (cycle123Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (cycle123Homeo_torus i) V g
  · intro g hg y _
    obtain ⟨t₁, t₂, t₃⟩ := y
    obtain ⟨V, hV, hVc, hy⟩ := hYc (t₁, t₂, t₃)
    refine exists_mem_coinvariants_forall_mid_eq (cycle123Ops χ) hV hVc hy ?_
    by_cases hrel : t₂ = t₃
    · subst hrel
      exact cycle123_fibre_sub_mem_of_eq hF χ hχ D hc hP t₁ t₂ (mem_sbSubmodule.mp hg)
    · exact cycle123_mem_fibreSpan_of_ne hF χ hu hrel
        (isSchwartzBruhat_fibreMid (mem_sbSubmodule.mp ((sbSubmodule _).sub_mem hg (hΘS g hg))) _)

end Cycle123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Cycle132

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private theorem cycle132_cTrans_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (cTrans v) - f ∈ fibreSpan (cycle132Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have h := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₂, t₃) (RootIndex.left13, v) hf
  have e : (cycle132Ops χ (RootIndex.left13, v)).fibreRelation (t₁, t₂, t₃) f =
      f ∘ (cTrans v) - f := by
    funext k
    show (1 : ℂ) * f (cTrans v k) - f k = f (cTrans v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem cycle132_rTrans_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (rTrans v) - f ∈ fibreSpan (cycle132Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have h := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₂, t₃) (RootIndex.right13, v) hf
  have e : (cycle132Ops χ (RootIndex.right13, v)).fibreRelation (t₁, t₂, t₃) f =
      f ∘ (rTrans v) - f := by
    funext k
    show (1 : ℂ) * f (rTrans v k) - f k = f (rTrans v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem cycle132_smul_comp_aTrans_sub_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t : Fˣ × Fˣ × Fˣ) (s : F) {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    χ s • (g ∘ (aTrans s)) - g ∈ fibreSpan (cycle132Ops χ) t := by
  obtain ⟨t₁, t₂, t₃⟩ := t
  have h₁ : χ s • ((g ∘ (aTrans s)) ∘ (cShearAdd (e := fun y : (F × F) × (F × F) => y.1.2 * s)
      (by fun_prop))) - g ∈ fibreSpan (cycle132Ops χ) (t₁, t₂, t₃) :=
    fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₂, t₃) (RootIndex.left12, s) hg
  exact smul_comp_sub_mem_of_bridge h₁ (comp_cShearAdd_sub_mem hF (cycle132_cTrans_sub_mem χ _) _
    (isSchwartzBruhat_comp_homeo hg _))

private theorem cycle132_mem_fibreSpan_of_ne [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    {u : F} (hu : χ u ≠ 1) {t₁ t₂ t₃ : Fˣ} (hne : t₁ ≠ t₂) {g : (F × F × F) × (F × F) → ℂ}
    (hg : IsSchwartzBruhat g) : g ∈ fibreSpan (cycle132Ops χ) (t₁, t₂, t₃) := by
  set ρ : F := ((t₁ * t₂⁻¹ : Fˣ) : F) with hρdef
  have hρ1 : ρ ≠ 1 := fun h => hne (mul_inv_eq_one.mp (Units.val_eq_one.mp h))
  have hρ : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hs := rescale_mul_eq_add u hρ
  refine mem_of_coeff_ne (M := fibreSpan (cycle132Ops χ) (t₁, t₂, t₃)) (P := IsSchwartzBruhat)
    (S := rShearAdd (e := fun z : (F × F × F) × F => z.2 * (u * (ρ - 1)⁻¹)) (by fun_prop))
    (B := aTrans (u * (ρ - 1)⁻¹ * ρ))
    (c₁ := χ (u * (ρ - 1)⁻¹)) (c₂ := χ (u * (ρ - 1)⁻¹ * ρ)) ?_ ?_ ?_ ?_ ?_ hg
  · exact addChar_apply_ne_of_eq_add χ hu hs
  · intro g hg
    exact isSchwartzBruhat_comp_homeo hg _
  · intro g hg
    exact comp_rShearAdd_sub_mem hF (cycle132_rTrans_sub_mem χ _) _ hg
  · intro g hg
    exact fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₂, t₃)
      (RootIndex.right23, u * (ρ - 1)⁻¹) hg
  · intro g hg
    exact cycle132_smul_comp_aTrans_sub_mem hF χ (t₁, t₂, t₃) (u * (ρ - 1)⁻¹ * ρ) hg

private theorem twistedSpan_cycleChar_le_cycle132 [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t₁ t₃ : Fˣ) : twistedSpan (cycleChar χ) ≤ fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) := by
  refine twistedSpan_cycleChar_le_of_axes χ ?_ ?_ ?_ ?_ ?_
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have hpure := cycle132_smul_comp_aTrans_sub_mem hF χ (t₁, t₁, t₃) s hg
    have e : twistedRel (cycleChar χ) (((s, 0, 0), 0) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (χ s • (g ∘ (aTrans s)) - g) := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, r⟩ := k
      show g (((a, b, c), (p, r)) + ((s, 0, 0), 0)) - (cycleChar χ ((s, 0, 0), 0))⁻¹ * g ((a, b, c), (p, r))
        = (χ s)⁻¹ * (χ s * g ((a + s, b, c), (p, r)) - g ((a, b, c), (p, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hpure
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) (RootIndex.left23, s) hg
    have e : twistedRel (cycleChar χ) (((0, s, 0), 0) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (cycle132Ops χ (RootIndex.left23, s)).fibreRelation (t₁, t₁, t₃) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, r⟩ := k
      show g (((a, b, c), (p, r)) + ((0, s, 0), 0)) - (cycleChar χ ((0, s, 0), 0))⁻¹ * g ((a, b, c), (p, r))
        = (χ s)⁻¹ * (χ s * g ((a, b + s, c), (p, r)) - g ((a, b, c), (p, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  ·
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) (RootIndex.left13, s) hg
    have e : twistedRel (cycleChar χ) (((0, 0, s), 0) : (F × F × F) × (F × F)) g =
        (cycle132Ops χ (RootIndex.left13, s)).fibreRelation (t₁, t₁, t₃) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, r⟩ := k
      show g (((a, b, c), (p, r)) + ((0, 0, s), 0)) - (cycleChar χ ((0, 0, s), 0))⁻¹ * g ((a, b, c), (p, r))
        = 1 * g ((a, b, c + s), (p, r)) - g ((a, b, c), (p, r))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁
  ·
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) (RootIndex.right12, s) hg
    have e : twistedRel (cycleChar χ) ((0, (s, 0)) : (F × F × F) × (F × F)) g =
        (χ s)⁻¹ • (cycle132Ops χ (RootIndex.right12, s)).fibreRelation (t₁, t₁, t₃) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, r⟩ := k
      show g (((a, b, c), (p, r)) + (0, (s, 0))) - (cycleChar χ (0, (s, 0)))⁻¹ * g ((a, b, c), (p, r))
        = (χ s)⁻¹ * (χ s * g ((a, b, c), (p + s, r)) - g ((a, b, c), (p, r)))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  ·
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) (RootIndex.right13, s) hg
    have e : twistedRel (cycleChar χ) ((0, (0, s)) : (F × F × F) × (F × F)) g =
        (cycle132Ops χ (RootIndex.right13, s)).fibreRelation (t₁, t₁, t₃) g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, r⟩ := k
      show g (((a, b, c), (p, r)) + (0, (0, s))) - (cycleChar χ (0, (0, s)))⁻¹ * g ((a, b, c), (p, r))
        = 1 * g ((a, b, c), (p, r + s)) - g ((a, b, c), (p, r))
      rw [cycleChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁

private theorem sub_comp_perm132_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F)))) (hP : D.IsAdmissibleAut perm132) (t₁ t₃ : Fˣ)
    {g : (F × F × F) × (F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g - (fun k => g (perm132 k)) ∈ fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) := by
  have hχK := isLocallyConstant_cycleChar χ hχ
  have hgs : IsSchwartzBruhat fun k => g (perm132 k) := isSchwartzBruhat_comp_homeo hg hP.homeo
  have hcomp : D.twistedIntegral (cycleChar χ) (fun k => g (perm132 k)) =
      D.twistedIntegral (cycleChar χ) g := by
    rw [D.twistedIntegral_comp (cycleChar χ) hP hχK hg, cycleChar_comp_perm132]
  have h0 : D.twistedIntegral (cycleChar χ) (g - fun k => g (perm132 k)) = 0 := by
    have h1 : (g - fun k => g (perm132 k)) = g - (1 : ℂ) • fun k => g (perm132 k) := by
      rw [one_smul]
    rw [h1, D.twistedIntegral_sub_smul (cycleChar χ) hχK hg hgs 1, hcomp]
    ring
  have hsub : IsSchwartzBruhat (g - fun k => g (perm132 k)) :=
    mem_sbSubmodule.mp ((sbSubmodule _).sub_mem (mem_sbSubmodule.mpr hg) (mem_sbSubmodule.mpr hgs))
  exact D.mem_of_twistedIntegral_eq_zero (cycleChar χ) hc hχK
    (twistedSpan_cycleChar_le_cycle132 hF χ t₁ t₃) hsub h0

private theorem cycle132_fibre_sub_mem_of_eq [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F)))) (hP : D.IsAdmissibleAut perm132) (t₁ t₃ : Fˣ)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    (fun k : (F × F × F) × (F × F) => (f - compLin cycle132InvolutionHomeomorph f) (k.1, ((t₁, t₁, t₃), k.2))) ∈
      fibreSpan (cycle132Ops χ) (t₁, t₁, t₃) := by
  have hG : IsSchwartzBruhat fun k : (F × F × F) × (F × F) => f (k.1, ((t₁, t₁, t₃), k.2)) :=
    isSchwartzBruhat_fibreMid hf _
  have e : (fun k : (F × F × F) × (F × F) => (f - compLin cycle132InvolutionHomeomorph f) (k.1, ((t₁, t₁, t₃), k.2))) =
      (fun k : (F × F × F) × (F × F) => f (k.1, ((t₁, t₁, t₃), k.2))) -
        fun k : (F × F × F) × (F × F) =>
          (fun k : (F × F × F) × (F × F) => f (k.1, ((t₁, t₁, t₃), k.2))) (perm132 k) := by
    funext k
    obtain ⟨⟨a, b, c⟩, p, r⟩ := k
    show f ((a, b, c), (t₁, t₁, t₃), (p, r)) - f (cycle132Involution ((a, b, c), (t₁, t₁, t₃), (p, r))) =
      f ((a, b, c), (t₁, t₁, t₃), (p, r)) - f ((a, p, r), (t₁, t₁, t₃), (b, c))
    rw [cycle132Involution_of_eq a b c p r t₁ t₁ t₃ rfl]
  rw [e]
  exact sub_comp_perm132_mem hF χ hχ D hc hP t₁ t₃ hG

private theorem cycle132_apply_comp_involution_eq [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F))) (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F))))
    (hP : D.IsAdmissibleAut perm132)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      T ((cycle132Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    T (f ∘ cycle132InvolutionHomeomorph) = T f := by
  obtain ⟨u, hu⟩ := AddChar.ne_one_iff.mp hχ1
  have hΘS : ∀ g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      compLin cycle132InvolutionHomeomorph g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :=
    fun g hg => mem_sbSubmodule.mpr (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hg) _)
  refine Localisation.apply_eq_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1) (fun i => (cycle132Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (compLin cycle132InvolutionHomeomorph) hΘS ?_ T
    hT (mem_sbSubmodule.mpr hf)
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (cycle132Homeo i) (cycle132Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (cycle132Homeo_torus i) V g
  · intro g hg y _
    obtain ⟨t₁, t₂, t₃⟩ := y
    obtain ⟨V, hV, hVc, hy⟩ := hYc (t₁, t₂, t₃)
    refine exists_mem_coinvariants_forall_mid_eq (cycle132Ops χ) hV hVc hy ?_
    by_cases hrel : t₁ = t₂
    · subst hrel
      exact cycle132_fibre_sub_mem_of_eq hF χ hχ D hc hP t₁ t₃ (mem_sbSubmodule.mp hg)
    · exact cycle132_mem_fibreSpan_of_ne hF χ hu hrel
        (isSchwartzBruhat_fibreMid (mem_sbSubmodule.mp ((sbSubmodule _).sub_mem hg (hΘS g hg))) _)

end Cycle132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

noncomputable section

open SchwartzBruhatIntegral LanglandsTunnell.TateLocal

namespace WhittakerCoinvariantsGL3

section Algebra

variable {K : Type*}

private theorem smul_comp_sub_mem_of_comp_sub_mem {M : Submodule ℂ (K → ℂ)} {g : K → ℂ} {B S : K → K}
    {c : ℂ} (h₁ : c • ((g ∘ B) ∘ S) - g ∈ M) (hS : (g ∘ B) ∘ S - g ∘ B ∈ M) :
    c • (g ∘ B) - g ∈ M := by
  have key : c • (g ∘ B) - g = (c • ((g ∘ B) ∘ S) - g) - c • ((g ∘ B) ∘ S - g ∘ B) := by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply]
    ring
  rw [key]
  exact M.sub_mem h₁ (M.smul_mem c hS)

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

section FibreMaps

private def bigTransA (v : F) : ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := ((k.1.1 + v, k.1.2.1, k.1.2.2), k.2)
  invFun k := ((k.1.1 - v, k.1.2.1, k.1.2.2), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def bigTransC (v : F) : ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + v), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - v), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def bigTransQ (v : F) : ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2.1 + v, k.2.2.2))
  invFun k := (k.1, (k.2.1, k.2.2.1 - v, k.2.2.2))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def bigTransR (v : F) : ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2.1, k.2.2.2 + v))
  invFun k := (k.1, (k.2.1, k.2.2.1, k.2.2.2 - v))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def bigShearC {e : (F × F) × (F × F × F) → F} (he : Continuous e) :
    ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := ((k.1.1, k.1.2.1, k.1.2.2 + e ((k.1.1, k.1.2.1), k.2)), k.2)
  invFun k := ((k.1.1, k.1.2.1, k.1.2.2 - e ((k.1.1, k.1.2.1), k.2)), k.2)
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def bigShearR {e : (F × F × F) × (F × F) → F} (he : Continuous e) :
    ((F × F × F) × (F × F × F)) ≃ₜ ((F × F × F) × (F × F × F)) where
  toFun k := (k.1, (k.2.1, k.2.2.1, k.2.2.2 + e (k.1, (k.2.1, k.2.2.1))))
  invFun k := (k.1, (k.2.1, k.2.2.1, k.2.2.2 - e (k.1, (k.2.1, k.2.2.1))))
  left_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  right_inv k := by
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private
theorem comp_bigShearC_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat f → f ∘ (bigTransC v) - f ∈ M)
    {e : (F × F) × (F × F × F) → F} (he : Continuous e) {g : (F × F × F) × (F × F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (bigShearC he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F) × (F × F × F)) := (hF.prod hF).prod (hF.prod (hF.prod hF))
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F × F)) hY
    (φ := fun k : (F × F × F) × (F × F × F) => ((k.1.1, k.1.2.1), k.2)) (by fun_prop) (fun v : F => bigTransC v)
    (fun v k => rfl) (bigShearC he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (bigTransC v))
      (sbSubmodule ((F × F × F) × (F × F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

private
theorem comp_bigShearR_sub_mem [T2Space F] (hF : HasClopenBasis F) {M : Submodule ℂ ((F × F × F) × (F × F × F) → ℂ)}
    (h13 : ∀ v : F, ∀ f : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat f → f ∘ (bigTransR v) - f ∈ M)
    {e : (F × F × F) × (F × F) → F} (he : Continuous e) {g : (F × F × F) × (F × F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g ∘ (bigShearR he) - g ∈ M := by
  have hY : HasClopenBasis ((F × F × F) × (F × F)) := (hF.prod (hF.prod hF)).prod (hF.prod hF)
  have hmem := comp_shear_sub_mem_coinvariants (X := (F × F × F) × (F × F × F)) hY
    (φ := fun k : (F × F × F) × (F × F × F) => (k.1, (k.2.1, k.2.2.1))) (by fun_prop) (fun v : F => bigTransR v)
    (fun v k => rfl) (bigShearR he) (c := e) (fun k => rfl) hg
  refine (show Localisation.coinvariants (fun v : F => compLin (bigTransR v))
      (sbSubmodule ((F × F × F) × (F × F × F))) ≤ M from ?_) hmem
  unfold Localisation.coinvariants
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, f, hf, rfl⟩
  exact h13 v f (mem_sbSubmodule.mp hf)

end FibreMaps
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section FibreData

private def bigChar (χ : AddChar F ℂ) : AddChar ((F × F × F) × (F × F × F)) ℂ where
  toFun k := χ k.1.1 * χ k.1.2.1 * χ k.2.1 * χ k.2.2.1
  map_zero_eq_one' := by
    simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem bigChar_apply (χ : AddChar F ℂ) (k : (F × F × F) × (F × F × F)) :
    bigChar χ k = χ k.1.1 * χ k.1.2.1 * χ k.2.1 * χ k.2.2.1 :=
  rfl

omit [IsTopologicalRing F] in
private theorem isLocallyConstant_bigChar (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x) :
    IsLocallyConstant fun k : (F × F × F) × (F × F × F) => bigChar χ k :=
  (((hχ.comp_continuous (continuous_fst.comp continuous_fst)).mul
    (hχ.comp_continuous (continuous_fst.comp (continuous_snd.comp continuous_fst)))).mul
    (hχ.comp_continuous (continuous_fst.comp continuous_snd))).mul
    (hχ.comp_continuous (continuous_fst.comp (continuous_snd.comp continuous_snd)))

private def bigPerm : ((F × F × F) × (F × F × F)) ≃+ ((F × F × F) × (F × F × F)) where
  toFun k := ((k.2.2.1, k.2.1, k.2.2.2), (k.1.2.1, k.1.1, k.1.2.2))
  invFun k := ((k.2.2.1, k.2.1, k.2.2.2), (k.1.2.1, k.1.1, k.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem bigChar_comp_bigPerm (χ : AddChar F ℂ) :
    (bigChar χ).compAddMonoidHom (bigPerm (F := F)).symm.toAddMonoidHom = bigChar χ := by
  refine AddChar.ext _ _ fun k => ?_
  obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
  show χ q * χ p * χ b * χ a = χ a * χ b * χ p * χ q
  ring

end FibreData
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Fibres

private theorem bigCell_transC_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (bigTransC v) - f ∈ fibreSpan (bigCellOps χ) t := by
  have h := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.left13, v) hf
  have e : (bigCellOps χ (RootIndex.left13, v)).fibreRelation t f = f ∘ (bigTransC v) - f := by
    funext k
    show (1 : ℂ) * f (bigTransC v k) - f k = f (bigTransC v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem bigCell_transR_sub_mem (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (v : F) (f : (F × F × F) × (F × F × F) → ℂ)
    (hf : IsSchwartzBruhat f) : f ∘ (bigTransR v) - f ∈ fibreSpan (bigCellOps χ) t := by
  have h := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.right13, v) hf
  have e : (bigCellOps χ (RootIndex.right13, v)).fibreRelation t f = f ∘ (bigTransR v) - f := by
    funext k
    show (1 : ℂ) * f (bigTransR v k) - f k = f (bigTransR v k) - f k
    rw [one_mul]
  rw [e] at h
  exact h

private theorem bigCell_smul_comp_transA_sub_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t : Fˣ × Fˣ × Fˣ) (s : F) {g : (F × F × F) × (F × F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    χ s • (g ∘ (bigTransA s)) - g ∈ fibreSpan (bigCellOps χ) t := by
  have h₁ : χ s • ((g ∘ (bigTransA s)) ∘ (bigShearC (e := fun y : (F × F) × (F × F × F) => y.1.2 * s)
      (by fun_prop))) - g ∈ fibreSpan (bigCellOps χ) t :=
    fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.left12, s) hg
  exact smul_comp_sub_mem_of_comp_sub_mem h₁ (comp_bigShearC_sub_mem hF (bigCell_transC_sub_mem χ _)
    _ (isSchwartzBruhat_comp_homeo hg _))

private theorem bigCell_smul_comp_transQ_sub_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t : Fˣ × Fˣ × Fˣ) (s : F) {g : (F × F × F) × (F × F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    χ s • (g ∘ (bigTransQ s)) - g ∈ fibreSpan (bigCellOps χ) t := by
  have h₁ : χ s • ((g ∘ (bigTransQ s)) ∘ (bigShearR (e := fun z : (F × F × F) × (F × F) => z.2.1 * s)
      (by fun_prop))) - g ∈ fibreSpan (bigCellOps χ) t :=
    fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.right23, s) hg
  exact smul_comp_sub_mem_of_comp_sub_mem h₁ (comp_bigShearR_sub_mem hF (bigCell_transR_sub_mem χ _)
    _ (isSchwartzBruhat_comp_homeo hg _))

private theorem twistedSpan_bigChar_le [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (t : Fˣ × Fˣ × Fˣ) : twistedSpan (bigChar χ) ≤ fibreSpan (bigCellOps χ) t := by
  have mem : ∀ {x : (F × F × F) × (F × F × F)},
      (∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
        twistedRel (bigChar χ) x g ∈ fibreSpan (bigCellOps χ) t) →
        x ∈ relationClosed (bigChar χ) (fibreSpan (bigCellOps χ) t) :=
    fun h => (mem_relationClosed_iff _ _ _).mpr h
  have hA : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) (((s, 0, 0), 0) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have hpure := bigCell_smul_comp_transA_sub_mem hF χ t s hg
    have e : twistedRel (bigChar χ) (((s, 0, 0), 0) : (F × F × F) × (F × F × F)) g =
        (χ s)⁻¹ • (χ s • (g ∘ (bigTransA s)) - g) := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + ((s, 0, 0), 0)) - (bigChar χ ((s, 0, 0), 0))⁻¹ * g ((a, b, c), (p, q, r))
        = (χ s)⁻¹ * (χ s * g ((a + s, b, c), (p, q, r)) - g ((a, b, c), (p, q, r)))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hpure
  have hB : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) (((0, s, 0), 0) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.left23, s) hg
    have e : twistedRel (bigChar χ) (((0, s, 0), 0) : (F × F × F) × (F × F × F)) g =
        (χ s)⁻¹ • (bigCellOps χ (RootIndex.left23, s)).fibreRelation t g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + ((0, s, 0), 0)) - (bigChar χ ((0, s, 0), 0))⁻¹ * g ((a, b, c), (p, q, r))
        = (χ s)⁻¹ * (χ s * g ((a, b + s, c), (p, q, r)) - g ((a, b, c), (p, q, r)))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  have hC : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) (((0, 0, s), 0) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.left13, s) hg
    have e : twistedRel (bigChar χ) (((0, 0, s), 0) : (F × F × F) × (F × F × F)) g =
        (bigCellOps χ (RootIndex.left13, s)).fibreRelation t g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + ((0, 0, s), 0)) - (bigChar χ ((0, 0, s), 0))⁻¹ * g ((a, b, c), (p, q, r))
        = 1 * g ((a, b, c + s), (p, q, r)) - g ((a, b, c), (p, q, r))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁
  have hP : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) ((0, (s, 0, 0)) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have r₁ := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.right12, s) hg
    have e : twistedRel (bigChar χ) ((0, (s, 0, 0)) : (F × F × F) × (F × F × F)) g =
        (χ s)⁻¹ • (bigCellOps χ (RootIndex.right12, s)).fibreRelation t g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + (0, (s, 0, 0))) - (bigChar χ (0, (s, 0, 0)))⁻¹ * g ((a, b, c), (p, q, r))
        = (χ s)⁻¹ * (χ s * g ((a, b, c), (p + s, q, r)) - g ((a, b, c), (p, q, r)))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ r₁
  have hQ : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) ((0, (0, s, 0)) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have hcs : χ s ≠ 0 := addChar_ne_zero χ s
    have hpure := bigCell_smul_comp_transQ_sub_mem hF χ t s hg
    have e : twistedRel (bigChar χ) ((0, (0, s, 0)) : (F × F × F) × (F × F × F)) g =
        (χ s)⁻¹ • (χ s • (g ∘ (bigTransQ s)) - g) := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + (0, (0, s, 0))) - (bigChar χ (0, (0, s, 0)))⁻¹ * g ((a, b, c), (p, q, r))
        = (χ s)⁻¹ * (χ s * g ((a, b, c), (p, q + s, r)) - g ((a, b, c), (p, q, r)))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, one_mul]
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ hpure
  have hR : ∀ s : F, ∀ g : (F × F × F) × (F × F × F) → ℂ, IsSchwartzBruhat g →
      twistedRel (bigChar χ) ((0, (0, 0, s)) : (F × F × F) × (F × F × F)) g ∈ fibreSpan (bigCellOps χ) t := by
    intro s g hg
    have r₁ := fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.right13, s) hg
    have e : twistedRel (bigChar χ) ((0, (0, 0, s)) : (F × F × F) × (F × F × F)) g =
        (bigCellOps χ (RootIndex.right13, s)).fibreRelation t g := by
      funext k
      obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
      show g (((a, b, c), (p, q, r)) + (0, (0, 0, s))) - (bigChar χ (0, (0, 0, s)))⁻¹ * g ((a, b, c), (p, q, r))
        = 1 * g ((a, b, c), (p, q, r + s)) - g ((a, b, c), (p, q, r))
      rw [bigChar_apply]
      simp only [Prod.mk_add_mk, add_zero, Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one,
        mul_one, inv_one, one_mul]
    rw [e]
    exact r₁
  refine twistedSpan_le_of_axes (bigChar χ) ?_ ?_
  · intro abc g hg
    obtain ⟨a, b, c⟩ := abc
    have hsum : (((a, b, c), 0) : (F × F × F) × (F × F × F)) = ((a, 0, 0), 0) + ((0, b, 0), 0) + ((0, 0, c), 0) := by
      ext <;> simp
    rw [hsum]
    exact (mem_relationClosed_iff _ _ _).mp ((relationClosed _ _).add_mem
      ((relationClosed _ _).add_mem (mem (hA a)) (mem (hB b))) (mem (hC c))) g hg
  · intro pqr g hg
    obtain ⟨p, q, r⟩ := pqr
    have hsum : ((0, (p, q, r)) : (F × F × F) × (F × F × F)) = (0, (p, 0, 0)) + (0, (0, q, 0)) + (0, (0, 0, r)) := by
      ext <;> simp
    rw [hsum]
    exact (mem_relationClosed_iff _ _ _).mp ((relationClosed _ _).add_mem
      ((relationClosed _ _).add_mem (mem (hP p)) (mem (hQ q))) (mem (hR r))) g hg

private theorem sub_comp_bigPerm_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F × F)))) (hP : D.IsAdmissibleAut bigPerm) (t : Fˣ × Fˣ × Fˣ)
    {g : (F × F × F) × (F × F × F) → ℂ} (hg : IsSchwartzBruhat g) :
    g - (fun k => g (bigPerm k)) ∈ fibreSpan (bigCellOps χ) t := by
  have hχK := isLocallyConstant_bigChar χ hχ
  have hgs : IsSchwartzBruhat fun k => g (bigPerm k) := isSchwartzBruhat_comp_homeo hg hP.homeo
  have hcomp : D.twistedIntegral (bigChar χ) (fun k => g (bigPerm k)) =
      D.twistedIntegral (bigChar χ) g := by
    rw [D.twistedIntegral_comp (bigChar χ) hP hχK hg, bigChar_comp_bigPerm]
  have h0 : D.twistedIntegral (bigChar χ) (g - fun k => g (bigPerm k)) = 0 := by
    have h1 : (g - fun k => g (bigPerm k)) = g - (1 : ℂ) • fun k => g (bigPerm k) := by
      rw [one_smul]
    rw [h1, D.twistedIntegral_sub_smul (bigChar χ) hχK hg hgs 1, hcomp]
    ring
  have hsub : IsSchwartzBruhat (g - fun k => g (bigPerm k)) :=
    mem_sbSubmodule.mp ((sbSubmodule _).sub_mem (mem_sbSubmodule.mpr hg) (mem_sbSubmodule.mpr hgs))
  exact D.mem_of_twistedIntegral_eq_zero (bigChar χ) hc hχK (twistedSpan_bigChar_le hF χ t) hsub h0

private theorem bigCell_fibre_sub_mem [T2Space F] (hF : HasClopenBasis F) (χ : AddChar F ℂ)
    (hχ : IsLocallyConstant fun x : F => χ x) (D : BallData ((F × F × F) × (F × F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F × F)))) (hP : D.IsAdmissibleAut bigPerm) (t : Fˣ × Fˣ × Fˣ)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    (fun k : (F × F × F) × (F × F × F) => (f - compLin bigCellInvolutionHomeomorph f) (k.1, (t, k.2))) ∈
      fibreSpan (bigCellOps χ) t := by
  have hG : IsSchwartzBruhat fun k : (F × F × F) × (F × F × F) => f (k.1, (t, k.2)) := isSchwartzBruhat_fibreMid hf _
  have e : (fun k : (F × F × F) × (F × F × F) => (f - compLin bigCellInvolutionHomeomorph f) (k.1, (t, k.2))) =
      (fun k : (F × F × F) × (F × F × F) => f (k.1, (t, k.2))) -
        fun k : (F × F × F) × (F × F × F) => (fun k : (F × F × F) × (F × F × F) => f (k.1, (t, k.2))) (bigPerm k) := by
    funext k
    obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
    rfl
  rw [e]
  exact sub_comp_bigPerm_mem hF χ hχ D hc hP t hG

end Fibres
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Main

private theorem bigCell_apply_comp_involution_eq [T2Space F] (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F × F))) (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F × F))))
    (hP : D.IsAdmissibleAut bigPerm)
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)),
      T ((bigCellOps χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → ℂ} (hf : IsSchwartzBruhat f) :
    T (f ∘ bigCellInvolutionHomeomorph) = T f := by
  have hΘS : ∀ g ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)),
      compLin bigCellInvolutionHomeomorph g ∈
        sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :=
    fun g hg => mem_sbSubmodule.mpr (isSchwartzBruhat_comp_homeo (mem_sbSubmodule.mp hg) _)
  refine Localisation.apply_eq_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) => x.2.1) (fun i => (bigCellOps χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (compLin bigCellInvolutionHomeomorph) hΘS ?_ T hT
    (mem_sbSubmodule.mpr hf)
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (bigCellHomeo i) (bigCellHomeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (bigCellHomeo_torus i) V g
  · intro g hg t _
    obtain ⟨V, hV, hVc, hy⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (bigCellOps χ) hV hVc hy
      (bigCell_fibre_sub_mem hF χ hχ D hc hP t (mem_sbSubmodule.mp hg))

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

private def unitriangular (x y z : F) : Matrix (Fin 3) (Fin 3) F := !![1, x, z; 0, 1, y; 0, 0, 1]

private def torus (t₁ t₂ t₃ : F) : Matrix (Fin 3) (Fin 3) F := !![t₁, 0, 0; 0, t₂, 0; 0, 0, t₃]

private def rootGen12 (c : F) : Matrix (Fin 3) (Fin 3) F := unitriangular c 0 0

private def rootGen23 (c : F) : Matrix (Fin 3) (Fin 3) F := unitriangular 0 c 0

private def rootGen13 (c : F) : Matrix (Fin 3) (Fin 3) F := unitriangular 0 0 c

private def longestWeyl : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private def refl12 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def refl23 : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

private def cycle123 : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private def cycle132 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

private def involution (g : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  longestWeyl * g.transpose * longestWeyl

section Transpose

variable (x y z t₁ t₂ t₃ : F)

private theorem unitriangular_transpose : (unitriangular x y z).transpose = !![1, 0, 0; x, 1, 0; z, y, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, unitriangular, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem torus_transpose : (torus t₁ t₂ t₃).transpose = torus t₁ t₂ t₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, torus, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one,
      Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk,
      Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem longestWeyl_transpose : (longestWeyl : Matrix (Fin 3) (Fin 3) F).transpose = longestWeyl := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, longestWeyl, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem refl12_transpose : (refl12 : Matrix (Fin 3) (Fin 3) F).transpose = refl12 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, refl12, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem refl23_transpose : (refl23 : Matrix (Fin 3) (Fin 3) F).transpose = refl23 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, refl23, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem cycle123_transpose : (cycle123 : Matrix (Fin 3) (Fin 3) F).transpose = cycle132 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, cycle123, cycle132, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

private theorem cycle132_transpose : (cycle132 : Matrix (Fin 3) (Fin 3) F).transpose = cycle123 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.transpose_apply, cycle123, cycle132, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq,
      Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Matrix.one_apply_ne,
      Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff]

end Transpose
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Involution

variable (x y z t₁ t₂ t₃ : F)

private theorem longestWeyl_mul_longestWeyl : (longestWeyl : Matrix (Fin 3) (Fin 3) F) * longestWeyl = 1 := by
  simp only [longestWeyl, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one, zero_add,
      Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem longestWeyl_mul_longestWeyl_mul (A : Matrix (Fin 3) (Fin 3) F) :
    longestWeyl * (longestWeyl * A) = A := by
  rw [← Matrix.mul_assoc, longestWeyl_mul_longestWeyl, Matrix.one_mul]

private theorem involution_mul (A B : Matrix (Fin 3) (Fin 3) F) :
    involution (A * B) = involution B * involution A := by
  simp only [involution, Matrix.transpose_mul, Matrix.mul_assoc, longestWeyl_mul_longestWeyl_mul]

private theorem involution_involution (A : Matrix (Fin 3) (Fin 3) F) : involution (involution A) = A := by
  simp only [involution, Matrix.transpose_mul, Matrix.transpose_transpose, longestWeyl_transpose,
    Matrix.mul_assoc, longestWeyl_mul_longestWeyl_mul, longestWeyl_mul_longestWeyl, Matrix.mul_one]

private theorem involution_unitriangular : involution (unitriangular x y z) = unitriangular y x z := by
  rw [involution, unitriangular_transpose]
  simp only [unitriangular, longestWeyl, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one,
      zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus : involution (torus t₁ t₂ t₃) = torus t₃ t₂ t₁ := by
  rw [involution, torus_transpose]
  simp only [torus, longestWeyl, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one, zero_add,
      Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus_mul_refl12 :
    involution (torus t₁ t₂ t₃ * refl12) = torus t₃ t₁ t₂ * refl23 := by
  rw [involution, Matrix.transpose_mul, torus_transpose, refl12_transpose]
  simp only [torus, longestWeyl, refl12, refl23, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero,
      mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus_mul_refl23 :
    involution (torus t₁ t₂ t₃ * refl23) = torus t₂ t₃ t₁ * refl12 := by
  rw [involution, Matrix.transpose_mul, torus_transpose, refl23_transpose]
  simp only [torus, longestWeyl, refl12, refl23, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero,
      mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus_mul_cycle123 :
    involution (torus t₁ t₂ t₃ * cycle123) = torus t₁ t₃ t₂ * cycle123 := by
  rw [involution, Matrix.transpose_mul, torus_transpose, cycle123_transpose]
  simp only [torus, longestWeyl, cycle123, cycle132, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero,
      mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus_mul_cycle132 :
    involution (torus t₁ t₂ t₃ * cycle132) = torus t₂ t₁ t₃ * cycle132 := by
  rw [involution, Matrix.transpose_mul, torus_transpose, cycle132_transpose]
  simp only [torus, longestWeyl, cycle123, cycle132, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero,
      mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

private theorem involution_torus_mul_longestWeyl :
    involution (torus t₁ t₂ t₃ * longestWeyl) = torus t₁ t₂ t₃ * longestWeyl := by
  rw [involution, Matrix.transpose_mul, torus_transpose, longestWeyl_transpose]
  simp only [torus, longestWeyl, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one, zero_add,
      Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul])

end Involution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Conjugation

variable {t₁ t₂ t₃ : F} (c : F)

private theorem rootGen12_mul_torus (h₁ : t₁ ≠ 0) :
    rootGen12 c * torus t₁ t₂ t₃ = torus t₁ t₂ t₃ * rootGen12 (t₂ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen12, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one,
      zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen23_mul_torus (h₂ : t₂ ≠ 0) :
    rootGen23 c * torus t₁ t₂ t₃ = torus t₁ t₂ t₃ * rootGen23 (t₃ * t₂⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen23, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one,
      zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen13_mul_torus (h₁ : t₁ ≠ 0) :
    rootGen13 c * torus t₁ t₂ t₃ = torus t₁ t₂ t₃ * rootGen13 (t₃ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen13, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero, add_zero, mul_one,
      zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen23_mul_torus_mul_refl12 (h₂ : t₂ ≠ 0) :
    rootGen23 c * (torus t₁ t₂ t₃ * refl12) = torus t₁ t₂ t₃ * refl12 * rootGen13 (t₃ * t₂⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero,
      add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen13_mul_torus_mul_refl12 (h₁ : t₁ ≠ 0) :
    rootGen13 c * (torus t₁ t₂ t₃ * refl12) = torus t₁ t₂ t₃ * refl12 * rootGen23 (t₃ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero,
      add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen12_mul_torus_mul_refl23 (h₁ : t₁ ≠ 0) :
    rootGen12 c * (torus t₁ t₂ t₃ * refl23) = torus t₁ t₂ t₃ * refl23 * rootGen13 (t₂ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero,
      add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen13_mul_torus_mul_refl23 (h₁ : t₁ ≠ 0) :
    rootGen13 c * (torus t₁ t₂ t₃ * refl23) = torus t₁ t₂ t₃ * refl23 * rootGen12 (t₃ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, Matrix.one_fin_three, mul_zero,
      add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff,
      Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen23_mul_torus_mul_cycle123 (h₂ : t₂ ≠ 0) :
    rootGen23 c * (torus t₁ t₂ t₃ * cycle123) = torus t₁ t₂ t₃ * cycle123 * rootGen12 (t₃ * t₂⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen12, rootGen23, cycle123, Matrix.mul_fin_three, Matrix.one_fin_three,
      mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq,
      Fin.zero_eq_one_iff, Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk,
      Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

private theorem rootGen12_mul_torus_mul_cycle132 (h₁ : t₁ ≠ 0) :
    rootGen12 c * (torus t₁ t₂ t₃ * cycle132) = torus t₁ t₂ t₃ * cycle132 * rootGen23 (t₂ * t₁⁻¹ * c) := by
  simp only [unitriangular, torus, rootGen12, rootGen23, cycle132, Matrix.mul_fin_three, Matrix.one_fin_three,
      mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq,
      Fin.zero_eq_one_iff, Nat.reduceAdd, OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk,
      Matrix.cons_val, Fin.reduceEq, Fin.one_eq_zero_iff, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [mul_zero, add_zero, mul_one, zero_add, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.one_apply_eq, Fin.mk_one, Matrix.cons_val_one, ne_eq, Fin.zero_eq_one_iff, Nat.reduceAdd,
      OfNat.ofNat_ne_one, not_false_eq_true, Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq,
      Fin.one_eq_zero_iff, one_mul, zero_mul] <;> (try field_simp))

end Conjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

private def lowerLeftMinor1 (g : Matrix (Fin 3) (Fin 3) F) : F := g 2 0

private def lowerLeftMinor2 (g : Matrix (Fin 3) (Fin 3) F) : F := g 1 0 * g 2 1 - g 1 1 * g 2 0

private def bigCell : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | lowerLeftMinor1 g ≠ 0 ∧ lowerLeftMinor2 g ≠ 0}

private def cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g ≠ 0}

private def cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | lowerLeftMinor1 g ≠ 0 ∧ lowerLeftMinor2 g = 0}

private def reflCell12 : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | lowerLeftMinor1 g = 0 ∧ g 2 1 = 0 ∧ g 1 0 ≠ 0}

private def reflCell23 : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | lowerLeftMinor1 g = 0 ∧ g 1 0 = 0 ∧ g 2 1 ≠ 0}

private def borelCell : Set (Matrix (Fin 3) (Fin 3) F) :=
  {g | g 1 0 = 0 ∧ lowerLeftMinor1 g = 0 ∧ g 2 1 = 0}

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

section Entries

variable (x y z : F)

@[scoped simp] private theorem unitriangular_apply_00 : unitriangular x y z 0 0 = 1 := rfl
@[scoped simp] private theorem unitriangular_apply_01 : unitriangular x y z 0 1 = x := rfl
@[scoped simp] private theorem unitriangular_apply_02 : unitriangular x y z 0 2 = z := rfl
@[scoped simp] private theorem unitriangular_apply_10 : unitriangular x y z 1 0 = 0 := rfl
@[scoped simp] private theorem unitriangular_apply_11 : unitriangular x y z 1 1 = 1 := rfl
@[scoped simp] private theorem unitriangular_apply_12 : unitriangular x y z 1 2 = y := rfl
@[scoped simp] private theorem unitriangular_apply_20 : unitriangular x y z 2 0 = 0 := rfl
@[scoped simp] private theorem unitriangular_apply_21 : unitriangular x y z 2 1 = 0 := rfl
@[scoped simp] private theorem unitriangular_apply_22 : unitriangular x y z 2 2 = 1 := rfl

@[scoped simp] private theorem longestWeyl_apply_00 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := rfl
@[scoped simp] private theorem longestWeyl_apply_01 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := rfl
@[scoped simp] private theorem longestWeyl_apply_02 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 0 2 = 1 := rfl
@[scoped simp] private theorem longestWeyl_apply_10 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := rfl
@[scoped simp] private theorem longestWeyl_apply_11 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 := rfl
@[scoped simp] private theorem longestWeyl_apply_12 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := rfl
@[scoped simp] private theorem longestWeyl_apply_20 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 2 0 = 1 := rfl
@[scoped simp] private theorem longestWeyl_apply_21 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := rfl
@[scoped simp] private theorem longestWeyl_apply_22 : (longestWeyl : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 := rfl

end Entries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

variable (g : Matrix (Fin 3) (Fin 3) F) (x y z : F)

private theorem lowerLeftMinor2_of_lowerLeftMinor1_eq_zero (h : lowerLeftMinor1 g = 0) :
    lowerLeftMinor2 g = g 1 0 * g 2 1 := by
  simp only [lowerLeftMinor1] at h
  simp [lowerLeftMinor2, h]

section Involution

private theorem involution_apply_one_zero : involution g 1 0 = g 2 1 := by
  simp [involution, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

private theorem involution_apply_two_one : involution g 2 1 = g 1 0 := by
  simp [involution, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

private theorem lowerLeftMinor1_involution : lowerLeftMinor1 (involution g) = lowerLeftMinor1 g := by
  simp [lowerLeftMinor1, involution, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

private theorem lowerLeftMinor2_involution : lowerLeftMinor2 (involution g) = lowerLeftMinor2 g := by
  simp [lowerLeftMinor2, involution, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

end Involution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

section Unitriangular

private theorem lowerLeftMinor1_unitriangular_mul : lowerLeftMinor1 (unitriangular x y z * g) = lowerLeftMinor1 g := by
  simp [lowerLeftMinor1, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerLeftMinor1_mul_unitriangular : lowerLeftMinor1 (g * unitriangular x y z) = lowerLeftMinor1 g := by
  simp [lowerLeftMinor1, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerLeftMinor2_unitriangular_mul : lowerLeftMinor2 (unitriangular x y z * g) = lowerLeftMinor2 g := by
  simp [lowerLeftMinor2, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem lowerLeftMinor2_mul_unitriangular : lowerLeftMinor2 (g * unitriangular x y z) = lowerLeftMinor2 g := by
  simp [lowerLeftMinor2, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem mul_unitriangular_apply_one_zero : (g * unitriangular x y z) 1 0 = g 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem unitriangular_mul_apply_two_one : (unitriangular x y z * g) 2 1 = g 2 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem unitriangular_mul_apply_one_zero : (unitriangular x y z * g) 1 0 = g 1 0 + y * g 2 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem mul_unitriangular_apply_two_one : (g * unitriangular x y z) 2 1 = g 2 1 + g 2 0 * x := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem unitriangular_mul_apply_one_zero_of_lowerLeftMinor1_eq_zero (h : lowerLeftMinor1 g = 0) :
    (unitriangular x y z * g) 1 0 = g 1 0 := by
  simp only [lowerLeftMinor1] at h
  rw [unitriangular_mul_apply_one_zero, h, mul_zero, add_zero]

private theorem mul_unitriangular_apply_two_one_of_lowerLeftMinor1_eq_zero (h : lowerLeftMinor1 g = 0) :
    (g * unitriangular x y z) 2 1 = g 2 1 := by
  simp only [lowerLeftMinor1] at h
  rw [mul_unitriangular_apply_two_one, h, zero_mul, add_zero]

end Unitriangular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F] (g : Matrix (Fin 3) (Fin 3) F)

private theorem mem_bigCell_iff : g ∈ bigCell ↔ lowerLeftMinor1 g ≠ 0 ∧ lowerLeftMinor2 g ≠ 0 := Iff.rfl

private theorem mem_cycleCell123_iff : g ∈ cycleCell123 ↔ lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g ≠ 0 := Iff.rfl

private theorem mem_cycleCell132_iff : g ∈ cycleCell132 ↔ lowerLeftMinor1 g ≠ 0 ∧ lowerLeftMinor2 g = 0 := Iff.rfl

private theorem mem_reflCell12_iff : g ∈ reflCell12 ↔ lowerLeftMinor1 g = 0 ∧ g 2 1 = 0 ∧ g 1 0 ≠ 0 := Iff.rfl

private theorem mem_reflCell23_iff : g ∈ reflCell23 ↔ lowerLeftMinor1 g = 0 ∧ g 1 0 = 0 ∧ g 2 1 ≠ 0 := Iff.rfl

private theorem mem_borelCell_iff : g ∈ borelCell ↔ g 1 0 = 0 ∧ lowerLeftMinor1 g = 0 ∧ g 2 1 = 0 := Iff.rfl

private theorem lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero (h : lowerLeftMinor1 g = 0) :
    lowerLeftMinor2 g = 0 ↔ g 1 0 = 0 ∨ g 2 1 = 0 := by
  simp only [lowerLeftMinor1] at h
  simp [lowerLeftMinor2, h]

private theorem mem_bigCell_or_mem_cells :
    g ∈ bigCell ∨ g ∈ cycleCell123 ∨ g ∈ cycleCell132 ∨ g ∈ reflCell12 ∨ g ∈ reflCell23 ∨ g ∈ borelCell := by
  by_cases h₁ : lowerLeftMinor1 g = 0
  · by_cases h₂ : lowerLeftMinor2 g = 0
    · rcases (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mp h₂ with h₁₀ | h₂₁
      · by_cases h₂₁ : g 2 1 = 0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((mem_borelCell_iff g).mpr ⟨h₁₀, h₁, h₂₁⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((mem_reflCell23_iff g).mpr ⟨h₁, h₁₀, h₂₁⟩)))))
      · by_cases h₁₀ : g 1 0 = 0
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((mem_borelCell_iff g).mpr ⟨h₁₀, h₁, h₂₁⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((mem_reflCell12_iff g).mpr ⟨h₁, h₂₁, h₁₀⟩))))
    · exact Or.inr (Or.inl ((mem_cycleCell123_iff g).mpr ⟨h₁, h₂⟩))
  · by_cases h₂ : lowerLeftMinor2 g = 0
    · exact Or.inr (Or.inr (Or.inl ((mem_cycleCell132_iff g).mpr ⟨h₁, h₂⟩)))
    · exact Or.inl ((mem_bigCell_iff g).mpr ⟨h₁, h₂⟩)

variable (F)

private theorem disjoint_cycleCell123_cycleCell132 :
    Disjoint (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) cycleCell132 :=
  Set.disjoint_left.mpr fun g h h' => ((mem_cycleCell132_iff g).mp h').1 ((mem_cycleCell123_iff g).mp h).1

private theorem disjoint_reflCell12_reflCell23 :
    Disjoint (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) reflCell23 :=
  Set.disjoint_left.mpr fun g h h' => ((mem_reflCell12_iff g).mp h).2.2 ((mem_reflCell23_iff g).mp h').2.1

private theorem reflCell12_eq :
    (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) =
      {g | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g = 0 ∧ g 1 0 ≠ 0} := by
  ext g
  simp only [mem_reflCell12_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₁, h₂₁, h₁₀⟩
    exact ⟨h₁, (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mpr (Or.inr h₂₁), h₁₀⟩
  · rintro ⟨h₁, h₂, h₁₀⟩
    refine ⟨h₁, ?_, h₁₀⟩
    rcases (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mp h₂ with h | h
    · exact absurd h h₁₀
    · exact h

private theorem reflCell23_eq :
    (reflCell23 : Set (Matrix (Fin 3) (Fin 3) F)) =
      {g | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g = 0 ∧ g 2 1 ≠ 0} := by
  ext g
  simp only [mem_reflCell23_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₁, h₁₀, h₂₁⟩
    exact ⟨h₁, (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mpr (Or.inl h₁₀), h₂₁⟩
  · rintro ⟨h₁, h₂, h₂₁⟩
    refine ⟨h₁, ?_, h₂₁⟩
    rcases (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mp h₂ with h | h
    · exact h
    · exact absurd h h₂₁

private theorem borelCell_eq :
    (borelCell : Set (Matrix (Fin 3) (Fin 3) F)) =
      {g | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g = 0 ∧ g 1 0 = 0 ∧ g 2 1 = 0} := by
  ext g
  simp only [mem_borelCell_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h₁₀, h₁, h₂₁⟩
    exact ⟨h₁, (lowerLeftMinor2_eq_zero_iff_of_lowerLeftMinor1_eq_zero g h₁).mpr (Or.inl h₁₀), h₁₀, h₂₁⟩
  · rintro ⟨h₁, -, h₁₀, h₂₁⟩
    exact ⟨h₁₀, h₁, h₂₁⟩

private theorem bigCell_union_cycleCells :
    (bigCell ∪ cycleCell123 ∪ cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F)) =
      {g | lowerLeftMinor1 g ≠ 0 ∨ lowerLeftMinor2 g ≠ 0} := by
  ext g
  simp only [Set.mem_union, mem_bigCell_iff, mem_cycleCell123_iff, mem_cycleCell132_iff, Set.mem_setOf_eq]
  tauto

private theorem stage_two_eq :
    ({g | lowerLeftMinor1 g ≠ 0 ∨ lowerLeftMinor2 g ≠ 0} \ bigCell : Set (Matrix (Fin 3) (Fin 3) F)) =
      cycleCell123 ∪ cycleCell132 := by
  ext g
  simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, mem_bigCell_iff, mem_cycleCell123_iff,
    mem_cycleCell132_iff]
  tauto

private theorem reflCells_eq :
    (reflCell12 ∪ reflCell23 : Set (Matrix (Fin 3) (Fin 3) F)) =
      {g | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g = 0} \ borelCell := by
  rw [reflCell12_eq, reflCell23_eq, borelCell_eq]
  ext g
  simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
  tauto

private theorem compl_borelCell :
    ((borelCell : Set (Matrix (Fin 3) (Fin 3) F))ᶜ) =
      bigCell ∪ cycleCell123 ∪ cycleCell132 ∪ (reflCell12 ∪ reflCell23) := by
  rw [bigCell_union_cycleCells, reflCells_eq, borelCell_eq]
  ext g
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_diff, Set.mem_setOf_eq]
  tauto

private theorem cycleCell123_eq_inter_closed :
    (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) =
      (cycleCell123 ∪ cycleCell132) ∩ {g | lowerLeftMinor1 g = 0} := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_union, mem_cycleCell123_iff, mem_cycleCell132_iff, Set.mem_setOf_eq]
  tauto

private theorem cycleCell123_eq_inter_open :
    (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) =
      (cycleCell123 ∪ cycleCell132) ∩ {g | lowerLeftMinor2 g ≠ 0} := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_union, mem_cycleCell123_iff, mem_cycleCell132_iff, Set.mem_setOf_eq]
  tauto

private theorem reflCell12_eq_inter_closed :
    (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) = (reflCell12 ∪ reflCell23) ∩ {g | g 2 1 = 0} := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_union, mem_reflCell12_iff, mem_reflCell23_iff, Set.mem_setOf_eq]
  tauto

private theorem reflCell12_eq_inter_open :
    (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) = (reflCell12 ∪ reflCell23) ∩ {g | g 1 0 ≠ 0} := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_union, mem_reflCell12_iff, mem_reflCell23_iff, Set.mem_setOf_eq]
  tauto

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F] (a b c s t₁ t₂ t₃ p q r : F)

private theorem unitriangular_mul_rootGen12' (u x y z : F) :
    unitriangular x y z * rootGen12 u = unitriangular (x + u) y z := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen12_assoc' (u x y z : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular x y z * (rootGen12 u * X) = unitriangular (x + u) y z * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen12']

private theorem unitriangular_mul_rootGen23' (u x y z : F) :
    unitriangular x y z * rootGen23 u = unitriangular x (y + u) (z + x * u) := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen23_assoc' (u x y z : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular x y z * (rootGen23 u * X) = unitriangular x (y + u) (z + x * u) * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen23']

private theorem unitriangular_mul_rootGen13' (u x y z : F) :
    unitriangular x y z * rootGen13 u = unitriangular x y (z + u) := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen13_assoc' (u x y z : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular x y z * (rootGen13 u * X) = unitriangular x y (z + u) * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen13']

private theorem torus_mul_rootGen12' {d₂ : F} (h : d₂ ≠ 0) (d₁ d₃ u : F) :
    torus d₁ d₂ d₃ * rootGen12 u = rootGen12 (u * d₁ * d₂⁻¹) * torus d₁ d₂ d₃ := by
  simp only [unitriangular, torus, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen12_assoc' {d₂ : F} (h : d₂ ≠ 0) (d₁ d₃ u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus d₁ d₂ d₃ * (rootGen12 u * X) = rootGen12 (u * d₁ * d₂⁻¹) * (torus d₁ d₂ d₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen12' h, Matrix.mul_assoc]

private theorem torus_mul_rootGen23' {d₃ : F} (h : d₃ ≠ 0) (d₁ d₂ u : F) :
    torus d₁ d₂ d₃ * rootGen23 u = rootGen23 (u * d₂ * d₃⁻¹) * torus d₁ d₂ d₃ := by
  simp only [unitriangular, torus, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen23_assoc' {d₃ : F} (h : d₃ ≠ 0) (d₁ d₂ u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus d₁ d₂ d₃ * (rootGen23 u * X) = rootGen23 (u * d₂ * d₃⁻¹) * (torus d₁ d₂ d₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen23' h, Matrix.mul_assoc]

private theorem torus_mul_rootGen13' {d₃ : F} (h : d₃ ≠ 0) (d₁ d₂ u : F) :
    torus d₁ d₂ d₃ * rootGen13 u = rootGen13 (u * d₁ * d₃⁻¹) * torus d₁ d₂ d₃ := by
  simp only [unitriangular, torus, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen13_assoc' {d₃ : F} (h : d₃ ≠ 0) (d₁ d₂ u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus d₁ d₂ d₃ * (rootGen13 u * X) = rootGen13 (u * d₁ * d₃⁻¹) * (torus d₁ d₂ d₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen13' h, Matrix.mul_assoc]

private theorem cycle123_mul_rootGen12' (u : F) :
    (cycle123 : Matrix (Fin 3) (Fin 3) F) * rootGen12 u = rootGen23 u * cycle123 := by
  simp only [unitriangular, rootGen12, rootGen23, cycle123, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem cycle123_mul_rootGen12_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (cycle123 : Matrix (Fin 3) (Fin 3) F) * (rootGen12 u * X) = rootGen23 u * (cycle123 * X) := by
  rw [← Matrix.mul_assoc, cycle123_mul_rootGen12', Matrix.mul_assoc]

private theorem cycle132_mul_rootGen23' (u : F) :
    (cycle132 : Matrix (Fin 3) (Fin 3) F) * rootGen23 u = rootGen12 u * cycle132 := by
  simp only [unitriangular, rootGen12, rootGen23, cycle132, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem cycle132_mul_rootGen23_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (cycle132 : Matrix (Fin 3) (Fin 3) F) * (rootGen23 u * X) = rootGen12 u * (cycle132 * X) := by
  rw [← Matrix.mul_assoc, cycle132_mul_rootGen23', Matrix.mul_assoc]

private theorem refl12_mul_rootGen23' (u : F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * rootGen23 u = rootGen13 u * refl12 := by
  simp only [unitriangular, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl12_mul_rootGen23_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * (rootGen23 u * X) = rootGen13 u * (refl12 * X) := by
  rw [← Matrix.mul_assoc, refl12_mul_rootGen23', Matrix.mul_assoc]

private theorem refl12_mul_rootGen13' (u : F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * rootGen13 u = rootGen23 u * refl12 := by
  simp only [unitriangular, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl12_mul_rootGen13_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * (rootGen13 u * X) = rootGen23 u * (refl12 * X) := by
  rw [← Matrix.mul_assoc, refl12_mul_rootGen13', Matrix.mul_assoc]

private theorem refl23_mul_rootGen12' (u : F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * rootGen12 u = rootGen13 u * refl23 := by
  simp only [unitriangular, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl23_mul_rootGen12_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * (rootGen12 u * X) = rootGen13 u * (refl23 * X) := by
  rw [← Matrix.mul_assoc, refl23_mul_rootGen12', Matrix.mul_assoc]

private theorem refl23_mul_rootGen13' (u : F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * rootGen13 u = rootGen12 u * refl23 := by
  simp only [unitriangular, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl23_mul_rootGen13_assoc' (u : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * (rootGen13 u * X) = rootGen12 u * (refl23 * X) := by
  rw [← Matrix.mul_assoc, refl23_mul_rootGen13', Matrix.mul_assoc]

private theorem unitriangular_zero_mul_rootGen12' (u y z : F) :
    unitriangular 0 y z * rootGen12 u = rootGen12 u * unitriangular 0 y (z - y * u) := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mid_zero_mul_rootGen23' (u x z : F) :
    unitriangular x 0 z * rootGen23 u = rootGen23 u * unitriangular x 0 (z + x * u) := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_first_mul_rootGen23' (u x : F) :
    unitriangular x 0 0 * rootGen23 u = rootGen23 u * (rootGen13 (x * u) * unitriangular x 0 0) := by
  simp only [unitriangular, rootGen23, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_first_mul_rootGen13' (u x : F) :
    unitriangular x 0 0 * rootGen13 u = rootGen13 u * unitriangular x 0 0 := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_second_mul_rootGen12' (u y : F) :
    unitriangular 0 y 0 * rootGen12 u = rootGen12 u * (rootGen13 (-(y * u)) * unitriangular 0 y 0) := by
  simp only [unitriangular, rootGen12, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_second_mul_rootGen13' (u y : F) :
    unitriangular 0 y 0 * rootGen13 u = rootGen13 u * unitriangular 0 y 0 := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen12_mul' (x y z : F) :
    unitriangular x y z = rootGen12 x * unitriangular 0 y (z - y * x) := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen23_mul' (x y z : F) :
    unitriangular x y z = rootGen23 y * unitriangular x 0 z := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen12_mul_rootGen13_mul' (x y z : F) :
    unitriangular x y z = rootGen12 x * (rootGen13 (z - y * x) * unitriangular 0 y 0) := by
  simp only [unitriangular, rootGen12, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen23_mul_rootGen13_mul' (x y z : F) :
    unitriangular x y z = rootGen23 y * (rootGen13 z * unitriangular x 0 0) := by
  simp only [unitriangular, rootGen23, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem torus_mul_unitriangular' {d₂ d₃ : F} (h₂ : d₂ ≠ 0) (h₃ : d₃ ≠ 0) (d₁ x y z : F) :
    torus d₁ d₂ d₃ * unitriangular x y z =
      unitriangular (x * d₁ * d₂⁻¹) (y * d₂ * d₃⁻¹) (z * d₁ * d₃⁻¹) * torus d₁ d₂ d₃ := by
  simp only [unitriangular, torus, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

section LeftMultiplication

private
theorem rootGen12_mul_unitriangular : rootGen12 s * unitriangular a b c = unitriangular (a + s) b (c + b * s) := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem rootGen23_mul_unitriangular : rootGen23 s * unitriangular a b c = unitriangular a (b + s) c := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem rootGen13_mul_unitriangular : rootGen13 s * unitriangular a b c = unitriangular a b (c + s) := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

end LeftMultiplication
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BigCell

private theorem bigCell_mul_rootGen12 :
    (unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p q r) * rootGen12 s =
      unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular (p + s) q r := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen12', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem bigCell_mul_rootGen23 :
    (unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p q r) * rootGen23 s =
      unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p (q + s) (r + p * s) := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen23', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem bigCell_mul_rootGen13 :
    (unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p q r) * rootGen13 s =
      unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p q (r + s) := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen13', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell123

private theorem cycleCell123_mul_rootGen12 (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 q r) * rootGen12 s =
      unitriangular a (b + s * t₂ * t₃⁻¹) (c + a * s * t₂ * t₃⁻¹) * torus t₁ t₂ t₃ * cycle123 *
          unitriangular 0 q (r - q * s) := by
  simp only [Matrix.mul_assoc, unitriangular_zero_mul_rootGen12', cycle123_mul_rootGen12_assoc',
    torus_mul_rootGen23_assoc' h₃, unitriangular_mul_rootGen23_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

private theorem cycleCell123_mul_rootGen23 :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 q r) * rootGen23 s =
      unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 (q + s) r := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen23', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem cycleCell123_mul_rootGen13 :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 q r) * rootGen13 s =
      unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 q (r + s) := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen13', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

end CycleCell123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell132

private theorem cycleCell132_mul_rootGen12 :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 r) * rootGen12 s =
      unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular (p + s) 0 r := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen12', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem cycleCell132_mul_rootGen23 (h₂ : t₂ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 r) * rootGen23 s =
      unitriangular (a + s * t₁ * t₂⁻¹) b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 (r + p * s) := by
  simp only [Matrix.mul_assoc, unitriangular_mid_zero_mul_rootGen23', cycle132_mul_rootGen23_assoc',
    torus_mul_rootGen12_assoc' h₂, unitriangular_mul_rootGen12_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

private theorem cycleCell132_mul_rootGen13 :
    (unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 r) * rootGen13 s =
      unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 (r + s) := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen13', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

end CycleCell132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell12

private theorem reflCell12_mul_rootGen12 :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl12 * unitriangular p 0 0) * rootGen12 s =
      unitriangular a b c * torus t₁ t₂ t₃ * refl12 * unitriangular (p + s) 0 0 := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen12', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem reflCell12_mul_rootGen23 (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl12 * unitriangular p 0 0) * rootGen23 s =
      unitriangular a (b + p * s * t₂ * t₃⁻¹) (c + a * p * s * t₂ * t₃⁻¹ + s * t₁ * t₃⁻¹) * torus t₁ t₂ t₃ *
          refl12 * unitriangular p 0 0 := by
  simp only [Matrix.mul_assoc, unitriangular_first_mul_rootGen23', refl12_mul_rootGen23_assoc',
    refl12_mul_rootGen13_assoc', torus_mul_rootGen13_assoc' h₃, torus_mul_rootGen23_assoc' h₃,
    unitriangular_mul_rootGen13_assoc', unitriangular_mul_rootGen23_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

private theorem reflCell12_mul_rootGen13 (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl12 * unitriangular p 0 0) * rootGen13 s =
      unitriangular a (b + s * t₂ * t₃⁻¹) (c + a * s * t₂ * t₃⁻¹) * torus t₁ t₂ t₃ * refl12 * unitriangular p 0 0 := by
  simp only [Matrix.mul_assoc, unitriangular_first_mul_rootGen13', refl12_mul_rootGen13_assoc',
    torus_mul_rootGen23_assoc' h₃, unitriangular_mul_rootGen23_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

end ReflCell12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell23

private theorem reflCell23_mul_rootGen12 (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0) * rootGen12 s =
      unitriangular (a - q * s * t₁ * t₂⁻¹) b (c + s * t₁ * t₃⁻¹) * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0 := by
  simp only [Matrix.mul_assoc, unitriangular_second_mul_rootGen12', refl23_mul_rootGen12_assoc',
    refl23_mul_rootGen13_assoc', torus_mul_rootGen13_assoc' h₃, torus_mul_rootGen12_assoc' h₂,
    unitriangular_mul_rootGen13_assoc', unitriangular_mul_rootGen12_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

private theorem reflCell23_mul_rootGen23 :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0) * rootGen23 s =
      unitriangular a b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 (q + s) 0 := by
  simp only [Matrix.mul_assoc, unitriangular_mul_rootGen23', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem reflCell23_mul_rootGen13 (h₂ : t₂ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0) * rootGen13 s =
      unitriangular (a + s * t₁ * t₂⁻¹) b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0 := by
  simp only [Matrix.mul_assoc, unitriangular_second_mul_rootGen13', refl23_mul_rootGen13_assoc',
    torus_mul_rootGen12_assoc' h₂, unitriangular_mul_rootGen12_assoc', zero_mul, mul_zero, zero_add, add_zero,
    sub_zero]
  all_goals ring_nf

end ReflCell23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BorelCell

private theorem borelCell_mul_rootGen12 (h₂ : t₂ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃) * rootGen12 s =
      unitriangular (a + s * t₁ * t₂⁻¹) b c * torus t₁ t₂ t₃ := by
  simp only [Matrix.mul_assoc, torus_mul_rootGen12' h₂, unitriangular_mul_rootGen12_assoc', zero_mul, mul_zero,
    zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem borelCell_mul_rootGen23 (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃) * rootGen23 s =
      unitriangular a (b + s * t₂ * t₃⁻¹) (c + a * s * t₂ * t₃⁻¹) * torus t₁ t₂ t₃ := by
  simp only [Matrix.mul_assoc, torus_mul_rootGen23' h₃, unitriangular_mul_rootGen23_assoc', zero_mul, mul_zero,
    zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem borelCell_mul_rootGen13 (h₃ : t₃ ≠ 0) :
    (unitriangular a b c * torus t₁ t₂ t₃) * rootGen13 s =
      unitriangular a b (c + s * t₁ * t₃⁻¹) * torus t₁ t₂ t₃ := by
  simp only [Matrix.mul_assoc, torus_mul_rootGen13' h₃, unitriangular_mul_rootGen13_assoc', zero_mul, mul_zero,
    zero_add, add_zero, sub_zero]
  all_goals ring_nf

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

private def bigCellChart (a b c t₁ t₂ t₃ p q r : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃ * longestWeyl * unitriangular p q r

private def bigCellInverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) × (F × F × F) :=
  (((g 0 0 * g 2 1 - g 0 1 * g 2 0) / lowerLeftMinor2 g, g 1 0 / g 2 0, g 0 0 / g 2 0),
    (g.det / lowerLeftMinor2 g, -lowerLeftMinor2 g / g 2 0, g 2 0),
    (g 2 1 / g 2 0, (g 1 0 * g 2 2 - g 1 2 * g 2 0) / lowerLeftMinor2 g, g 2 2 / g 2 0))

private def cycleCell123Chart (a b c t₁ t₂ t₃ q r : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃ * cycle123 * unitriangular 0 q r

private def cycleCell123Inverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) × (F × F) :=
  ((g 0 0 / g 1 0, g 1 1 / g 2 1, g 0 1 / g 2 1),
    (g.det / (g 1 0 * g 2 1), g 1 0, g 2 1),
    (g 2 2 / g 2 1, -(g 1 1 * g 2 2 - g 1 2 * g 2 1) / (g 1 0 * g 2 1)))

private def cycleCell132Chart (a b c t₁ t₂ t₃ p r : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃ * cycle132 * unitriangular p 0 r

private def cycleCell132Inverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) × (F × F) :=
  (((g 0 0 * g 2 2 - g 0 2 * g 2 0) / (g 1 0 * g 2 2 - g 1 2 * g 2 0), g 1 0 / g 2 0, g 0 0 / g 2 0),
    (-(g 0 0 * g 2 1 - g 0 1 * g 2 0) / g 2 0, -(g 1 0 * g 2 2 - g 1 2 * g 2 0) / g 2 0, g 2 0),
    (g 2 1 / g 2 0, g 2 2 / g 2 0))

private def reflCell12Chart (a b c t₁ t₂ t₃ p : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃ * refl12 * unitriangular p 0 0

private def reflCell12Inverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) × F :=
  ((g 0 0 / g 1 0, g 1 2 / g 2 2, g 0 2 / g 2 2),
    (-(g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 0, g 1 0, g 2 2),
    g 1 1 / g 1 0)

private def reflCell23Chart (a b c t₁ t₂ t₃ q : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃ * refl23 * unitriangular 0 q 0

private def reflCell23Inverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) × F :=
  (((g 0 1 * g 2 2 - g 0 2 * g 2 1) / (g 1 1 * g 2 2 - g 1 2 * g 2 1), g 1 1 / g 2 1, g 0 1 / g 2 1),
    (g 0 0, -(g 1 1 * g 2 2 - g 1 2 * g 2 1) / g 2 1, g 2 1),
    g 2 2 / g 2 1)

private def borelCellChart (a b c t₁ t₂ t₃ : F) : Matrix (Fin 3) (Fin 3) F :=
  unitriangular a b c * torus t₁ t₂ t₃

private def borelCellInverse (g : Matrix (Fin 3) (Fin 3) F) : (F × F × F) × (F × F × F) :=
  ((g 0 1 / g 1 1, g 1 2 / g 2 2, g 0 2 / g 2 2), (g 0 0, g 1 1, g 2 2))

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F] (a b c t₁ t₂ t₃ p q r : F) (g : Matrix (Fin 3) (Fin 3) F)

section BigCell

private theorem lowerLeftMinor1_bigCellChart : lowerLeftMinor1 (bigCellChart a b c t₁ t₂ t₃ p q r) = t₃ := by
  simp [lowerLeftMinor1, bigCellChart, unitriangular, torus, longestWeyl, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem lowerLeftMinor2_bigCellChart : lowerLeftMinor2 (bigCellChart a b c t₁ t₂ t₃ p q r) = -(t₂ * t₃) := by
  simp [lowerLeftMinor2, bigCellChart, unitriangular, torus, longestWeyl, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem det_bigCellChart : (bigCellChart a b c t₁ t₂ t₃ p q r).det = -(t₁ * t₂ * t₃) := by
  simp [Matrix.det_fin_three, bigCellChart, unitriangular, torus, longestWeyl]
  ring

private theorem bigCellChart_mem (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) : bigCellChart a b c t₁ t₂ t₃ p q r ∈ bigCell := by
  show lowerLeftMinor1 _ ≠ 0 ∧ lowerLeftMinor2 _ ≠ 0
  rw [lowerLeftMinor1_bigCellChart, lowerLeftMinor2_bigCellChart]
  exact ⟨h₃, by simp [h₂, h₃]⟩

private theorem bigCellInverse_bigCellChart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    bigCellInverse (bigCellChart a b c t₁ t₂ t₃ p q r) = ((a, b, c), (t₁, t₂, t₃), (p, q, r)) := by
  simp only [bigCellInverse]
  rw [lowerLeftMinor2_bigCellChart, det_bigCellChart]
  ext <;> simp [bigCellChart, unitriangular, torus, longestWeyl, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp) <;> ring

private theorem bigCellChart_bigCellInverse (hg : g ∈ bigCell) :
    bigCellChart (bigCellInverse g).1.1 (bigCellInverse g).1.2.1 (bigCellInverse g).1.2.2
        (bigCellInverse g).2.1.1 (bigCellInverse g).2.1.2.1 (bigCellInverse g).2.1.2.2
        (bigCellInverse g).2.2.1 (bigCellInverse g).2.2.2.1 (bigCellInverse g).2.2.2.2 = g := by
  obtain ⟨h₁, h₂⟩ := hg
  simp only [lowerLeftMinor1] at h₁
  simp only [bigCellChart, bigCellInverse, Matrix.det_fin_three, unitriangular, torus, longestWeyl,
    Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> (try simp only [lowerLeftMinor2]) <;> ring)

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell123

private theorem lowerLeftMinor1_cycleCell123Chart : lowerLeftMinor1 (cycleCell123Chart a b c t₁ t₂ t₃ q r) = 0 := by
  simp [lowerLeftMinor1, cycleCell123Chart, unitriangular, torus, cycle123, Matrix.mul_apply, Fin.sum_univ_succ]

private
theorem lowerLeftMinor2_cycleCell123Chart : lowerLeftMinor2 (cycleCell123Chart a b c t₁ t₂ t₃ q r) = t₂ * t₃ := by
  simp [lowerLeftMinor2, cycleCell123Chart, unitriangular, torus, cycle123, Matrix.mul_apply,
      Fin.sum_univ_succ]

private theorem det_cycleCell123Chart : (cycleCell123Chart a b c t₁ t₂ t₃ q r).det = t₁ * t₂ * t₃ := by
  simp [Matrix.det_fin_three, cycleCell123Chart, unitriangular, torus, cycle123]
  ring

private theorem cycleCell123Chart_mem (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    cycleCell123Chart a b c t₁ t₂ t₃ q r ∈ cycleCell123 := by
  show lowerLeftMinor1 _ = 0 ∧ lowerLeftMinor2 _ ≠ 0
  rw [lowerLeftMinor1_cycleCell123Chart, lowerLeftMinor2_cycleCell123Chart]
  exact ⟨rfl, mul_ne_zero h₂ h₃⟩

private theorem cycleCell123Inverse_cycleCell123Chart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    cycleCell123Inverse (cycleCell123Chart a b c t₁ t₂ t₃ q r) = ((a, b, c), (t₁, t₂, t₃), (q, r)) := by
  simp only [cycleCell123Inverse]
  rw [det_cycleCell123Chart]
  ext <;> simp [cycleCell123Chart, unitriangular, torus, cycle123, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp)
  ring

private theorem cycleCell123Chart_cycleCell123Inverse (hg : g ∈ cycleCell123) :
    cycleCell123Chart (cycleCell123Inverse g).1.1 (cycleCell123Inverse g).1.2.1 (cycleCell123Inverse g).1.2.2
        (cycleCell123Inverse g).2.1.1 (cycleCell123Inverse g).2.1.2.1 (cycleCell123Inverse g).2.1.2.2
        (cycleCell123Inverse g).2.2.1 (cycleCell123Inverse g).2.2.2 = g := by
  obtain ⟨h₀, h₂⟩ := hg
  simp only [lowerLeftMinor1, lowerLeftMinor2] at h₀ h₂
  rw [h₀, mul_zero, sub_zero] at h₂
  have h₁₀ : g 1 0 ≠ 0 := left_ne_zero_of_mul h₂
  have h₂₁ : g 2 1 ≠ 0 := right_ne_zero_of_mul h₂
  simp only [cycleCell123Chart, cycleCell123Inverse, Matrix.det_fin_three, unitriangular, torus, cycle123, h₀,
    Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val, h₀] <;> (try field_simp) <;> ring)

end CycleCell123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell132

private theorem lowerLeftMinor1_cycleCell132Chart : lowerLeftMinor1 (cycleCell132Chart a b c t₁ t₂ t₃ p r) = t₃ := by
  simp [lowerLeftMinor1, cycleCell132Chart, unitriangular, torus, cycle132, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem lowerLeftMinor2_cycleCell132Chart : lowerLeftMinor2 (cycleCell132Chart a b c t₁ t₂ t₃ p r) = 0 := by
  simp [lowerLeftMinor2, cycleCell132Chart, unitriangular, torus, cycle132, Matrix.mul_apply,
      Fin.sum_univ_succ]
  ring

private theorem det_cycleCell132Chart : (cycleCell132Chart a b c t₁ t₂ t₃ p r).det = t₁ * t₂ * t₃ := by
  simp [Matrix.det_fin_three, cycleCell132Chart, unitriangular, torus, cycle132]
  ring

private theorem cycleCell132Chart_mem (h₃ : t₃ ≠ 0) : cycleCell132Chart a b c t₁ t₂ t₃ p r ∈ cycleCell132 := by
  show lowerLeftMinor1 _ ≠ 0 ∧ lowerLeftMinor2 _ = 0
  rw [lowerLeftMinor1_cycleCell132Chart, lowerLeftMinor2_cycleCell132Chart]
  exact ⟨h₃, rfl⟩

private theorem cycleCell132Chart_denominator :
    cycleCell132Chart a b c t₁ t₂ t₃ p r 1 0 * cycleCell132Chart a b c t₁ t₂ t₃ p r 2 2 -
        cycleCell132Chart a b c t₁ t₂ t₃ p r 1 2 * cycleCell132Chart a b c t₁ t₂ t₃ p r 2 0 = -(t₂ * t₃) := by
  simp [cycleCell132Chart, unitriangular, torus, cycle132, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem cycleCell132Inverse_cycleCell132Chart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    cycleCell132Inverse (cycleCell132Chart a b c t₁ t₂ t₃ p r) = ((a, b, c), (t₁, t₂, t₃), (p, r)) := by
  simp only [cycleCell132Inverse]
  rw [cycleCell132Chart_denominator]
  ext <;> simp [cycleCell132Chart, unitriangular, torus, cycle132, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp) <;> ring

private theorem cycleCell132_denominator_ne_zero (hg : g ∈ cycleCell132) (hdet : g.det ≠ 0) :
    g 1 0 * g 2 2 - g 1 2 * g 2 0 ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := hg
  simp only [lowerLeftMinor1, lowerLeftMinor2] at h₁ h₂
  intro h
  apply mul_ne_zero hdet h₁
  rw [Matrix.det_fin_three]
  linear_combination (g 0 0 * g 2 1 - g 0 1 * g 2 0) * h + (g 0 2 * g 2 0 - g 0 0 * g 2 2) * h₂

private theorem cycleCell132Chart_cycleCell132Inverse (hg : g ∈ cycleCell132) (hdet : g.det ≠ 0) :
    cycleCell132Chart (cycleCell132Inverse g).1.1 (cycleCell132Inverse g).1.2.1 (cycleCell132Inverse g).1.2.2
        (cycleCell132Inverse g).2.1.1 (cycleCell132Inverse g).2.1.2.1 (cycleCell132Inverse g).2.1.2.2
        (cycleCell132Inverse g).2.2.1 (cycleCell132Inverse g).2.2.2 = g := by
  have hden := cycleCell132_denominator_ne_zero g hg hdet
  obtain ⟨h₁, h₂⟩ := hg
  simp only [lowerLeftMinor1, lowerLeftMinor2] at h₁ h₂
  have h₁₁ : g 1 1 = g 1 0 * g 2 1 / g 2 0 := (eq_div_iff h₁).mpr (sub_eq_zero.mp h₂).symm
  simp only [cycleCell132Inverse]
  set e := g 1 0 * g 2 2 - g 1 2 * g 2 0 with he
  simp only [cycleCell132Chart, unitriangular, torus, cycle132, h₁₁, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val, h₁₁] <;> (try field_simp) <;> (try simp only [he]) <;> ring)

end CycleCell132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell12

private theorem det_reflCell12Chart : (reflCell12Chart a b c t₁ t₂ t₃ p).det = -(t₁ * t₂ * t₃) := by
  simp [Matrix.det_fin_three, reflCell12Chart, unitriangular, torus, refl12]
  ring

private theorem reflCell12Chart_mem (h₂ : t₂ ≠ 0) : reflCell12Chart a b c t₁ t₂ t₃ p ∈ reflCell12 := by
  show lowerLeftMinor1 _ = 0 ∧ _ = 0 ∧ _ ≠ 0
  simp [lowerLeftMinor1, reflCell12Chart, unitriangular, torus, refl12, Matrix.mul_apply, Fin.sum_univ_succ, h₂]

private theorem reflCell12Inverse_reflCell12Chart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    reflCell12Inverse (reflCell12Chart a b c t₁ t₂ t₃ p) = ((a, b, c), (t₁, t₂, t₃), p) := by
  ext <;> simp [reflCell12Inverse, reflCell12Chart, unitriangular, torus, refl12, Matrix.mul_apply,
    Fin.sum_univ_succ] <;> (try field_simp)
  ring

private theorem reflCell12_apply_two_two_ne_zero (hg : g ∈ reflCell12) (hdet : g.det ≠ 0) : g 2 2 ≠ 0 := by
  obtain ⟨h₀, h₂₁, -⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  intro h
  apply hdet
  rw [Matrix.det_fin_three]
  simp [h₀, h₂₁, h]

private theorem reflCell12Chart_reflCell12Inverse (hg : g ∈ reflCell12) (hdet : g.det ≠ 0) :
    reflCell12Chart (reflCell12Inverse g).1.1 (reflCell12Inverse g).1.2.1 (reflCell12Inverse g).1.2.2
        (reflCell12Inverse g).2.1.1 (reflCell12Inverse g).2.1.2.1 (reflCell12Inverse g).2.1.2.2
        (reflCell12Inverse g).2.2 = g := by
  have h₂₂ := reflCell12_apply_two_two_ne_zero g hg hdet
  obtain ⟨h₀, h₂₁, h₁₀⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  simp only [reflCell12Chart, reflCell12Inverse, unitriangular, torus, refl12, h₀, h₂₁, Matrix.mul_fin_three, mul_zero,
    add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val, h₀, h₂₁] <;> (try field_simp) <;> ring)

end ReflCell12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell23

private theorem det_reflCell23Chart : (reflCell23Chart a b c t₁ t₂ t₃ q).det = -(t₁ * t₂ * t₃) := by
  simp [Matrix.det_fin_three, reflCell23Chart, unitriangular, torus, refl23]
  ring

private theorem reflCell23Chart_mem (h₃ : t₃ ≠ 0) : reflCell23Chart a b c t₁ t₂ t₃ q ∈ reflCell23 := by
  show lowerLeftMinor1 _ = 0 ∧ _ = 0 ∧ _ ≠ 0
  simp [lowerLeftMinor1, reflCell23Chart, unitriangular, torus, refl23, Matrix.mul_apply, Fin.sum_univ_succ, h₃]

private theorem reflCell23Chart_denominator :
    reflCell23Chart a b c t₁ t₂ t₃ q 1 1 * reflCell23Chart a b c t₁ t₂ t₃ q 2 2 -
        reflCell23Chart a b c t₁ t₂ t₃ q 1 2 * reflCell23Chart a b c t₁ t₂ t₃ q 2 1 = -(t₂ * t₃) := by
  simp [reflCell23Chart, unitriangular, torus, refl23, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem reflCell23Inverse_reflCell23Chart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    reflCell23Inverse (reflCell23Chart a b c t₁ t₂ t₃ q) = ((a, b, c), (t₁, t₂, t₃), q) := by
  simp only [reflCell23Inverse]
  rw [reflCell23Chart_denominator]
  ext <;> simp [reflCell23Chart, unitriangular, torus, refl23, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp)
  ring

private theorem reflCell23_denominator_ne_zero (hg : g ∈ reflCell23) (hdet : g.det ≠ 0) :
    g 1 1 * g 2 2 - g 1 2 * g 2 1 ≠ 0 := by
  obtain ⟨h₀, h₁₀, -⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  intro h
  apply hdet
  rw [Matrix.det_fin_three]
  linear_combination g 0 0 * h + (g 0 2 * g 2 1 - g 0 1 * g 2 2) * h₁₀ + (g 0 1 * g 1 2 - g 0 2 * g 1 1) * h₀

private theorem reflCell23Chart_reflCell23Inverse (hg : g ∈ reflCell23) (hdet : g.det ≠ 0) :
    reflCell23Chart (reflCell23Inverse g).1.1 (reflCell23Inverse g).1.2.1 (reflCell23Inverse g).1.2.2
        (reflCell23Inverse g).2.1.1 (reflCell23Inverse g).2.1.2.1 (reflCell23Inverse g).2.1.2.2
        (reflCell23Inverse g).2.2 = g := by
  have hden := reflCell23_denominator_ne_zero g hg hdet
  obtain ⟨h₀, h₁₀, h₂₁⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  simp only [reflCell23Inverse]
  set e := g 1 1 * g 2 2 - g 1 2 * g 2 1 with he
  simp only [reflCell23Chart, unitriangular, torus, refl23, h₀, h₁₀, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val, h₀, h₁₀] <;> (try field_simp) <;> (try simp only [he]) <;> ring)

end ReflCell23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BorelCell

private theorem det_borelCellChart : (borelCellChart a b c t₁ t₂ t₃).det = t₁ * t₂ * t₃ := by
  simp [Matrix.det_fin_three, borelCellChart, unitriangular, torus]

private theorem borelCellChart_mem : borelCellChart a b c t₁ t₂ t₃ ∈ borelCell := by
  show _ = 0 ∧ lowerLeftMinor1 _ = 0 ∧ _ = 0
  simp [lowerLeftMinor1, borelCellChart, unitriangular, torus, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem borelCellInverse_borelCellChart (h₂ : t₂ ≠ 0) (h₃ : t₃ ≠ 0) :
    borelCellInverse (borelCellChart a b c t₁ t₂ t₃) = ((a, b, c), (t₁, t₂, t₃)) := by
  ext <;> simp [borelCellInverse, borelCellChart, unitriangular, torus, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    (try field_simp)

private theorem borelCell_apply_one_one_ne_zero (hg : g ∈ borelCell) (hdet : g.det ≠ 0) : g 1 1 ≠ 0 := by
  obtain ⟨h₁₀, h₀, h₂₁⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  intro h
  apply hdet
  rw [Matrix.det_fin_three]
  simp [h₁₀, h₀, h₂₁, h]

private theorem borelCell_apply_two_two_ne_zero (hg : g ∈ borelCell) (hdet : g.det ≠ 0) : g 2 2 ≠ 0 := by
  obtain ⟨h₁₀, h₀, h₂₁⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  intro h
  apply hdet
  rw [Matrix.det_fin_three]
  simp [h₁₀, h₀, h₂₁, h]

private theorem borelCellChart_borelCellInverse (hg : g ∈ borelCell) (hdet : g.det ≠ 0) :
    borelCellChart (borelCellInverse g).1.1 (borelCellInverse g).1.2.1 (borelCellInverse g).1.2.2
        (borelCellInverse g).2.1 (borelCellInverse g).2.2.1 (borelCellInverse g).2.2.2 = g := by
  have h₁₁ := borelCell_apply_one_one_ne_zero g hg hdet
  have h₂₂ := borelCell_apply_two_two_ne_zero g hg hdet
  obtain ⟨h₁₀, h₀, h₂₁⟩ := hg
  simp only [lowerLeftMinor1] at h₀
  simp only [borelCellChart, borelCellInverse, unitriangular, torus, h₁₀, h₀, h₂₁, Matrix.mul_fin_three, mul_zero,
    add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val, h₁₀, h₀, h₂₁] <;> (try field_simp) <;> ring)

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F] (a b c t₁ t₂ t₃ p q r : F)

private theorem involution_bigCellChart :
    involution (bigCellChart a b c t₁ t₂ t₃ p q r) =
      bigCellChart q p r t₁ t₂ t₃ b a c := by
  simp only [bigCellChart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_longestWeyl]
  simp only [Matrix.mul_assoc, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem involution_cycleCell123Chart (h₂ : t₂ ≠ 0) :
    involution (cycleCell123Chart a b c t₁ t₂ t₃ q r) =
      cycleCell123Chart q (b * t₃ / t₂) ((b * q * t₃ + r * t₂) / t₂) t₁ t₃ t₂ a (-a * b + c) := by
  have e : (b * q * t₃ + r * t₂) / t₂ = r + q * (b * t₃ * t₂⁻¹) := by
    field_simp
    ring
  rw [e]
  simp only [cycleCell123Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_cycle123, unitriangular_eq_rootGen12_mul' b a c]
  simp only [Matrix.mul_assoc, cycle123_mul_rootGen12_assoc', torus_mul_rootGen23_assoc' h₂,
    unitriangular_mul_rootGen23_assoc', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem involution_cycleCell132Chart (h₁ : t₁ ≠ 0) :
    involution (cycleCell132Chart a b c t₁ t₂ t₃ p r) =
      cycleCell132Chart (a * t₂ / t₁) p r t₂ t₁ t₃ b c := by
  simp only [cycleCell132Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_cycle132, unitriangular_eq_rootGen23_mul' b a c]
  simp only [Matrix.mul_assoc, cycle132_mul_rootGen23_assoc', torus_mul_rootGen12_assoc' h₁,
    unitriangular_mul_rootGen12_assoc', zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem involution_reflCell12Chart (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    involution (reflCell12Chart a b c t₁ t₂ t₃ p) =
      reflCell23Chart ((-a * b * t₃ + c * t₃) / t₁) p (b * t₃ / t₂) t₃ t₁ t₂ a := by
  simp only [reflCell12Chart, reflCell23Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_refl12, unitriangular_eq_rootGen12_mul_rootGen13_mul' b a c]
  simp only [Matrix.mul_assoc, refl23_mul_rootGen12_assoc', refl23_mul_rootGen13_assoc', torus_mul_rootGen13_assoc' h₂,
    torus_mul_rootGen12_assoc' h₁, unitriangular_mul_rootGen13_assoc', unitriangular_mul_rootGen12_assoc', zero_mul,
    mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem involution_reflCell23Chart (h₁ : t₁ ≠ 0) :
    involution (reflCell23Chart a b c t₁ t₂ t₃ q) =
      reflCell12Chart q (c * t₃ / t₁) ((a * t₂ + c * q * t₃) / t₁) t₂ t₃ t₁ b := by
  simp only [reflCell23Chart, reflCell12Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_refl23, unitriangular_eq_rootGen23_mul_rootGen13_mul' b a c]
  simp only [Matrix.mul_assoc, refl12_mul_rootGen23_assoc', refl12_mul_rootGen13_assoc', torus_mul_rootGen13_assoc' h₁,
    torus_mul_rootGen23_assoc' h₁, unitriangular_mul_rootGen13_assoc', unitriangular_mul_rootGen23_assoc', zero_mul,
    mul_zero, zero_add, add_zero, sub_zero]
  all_goals ring_nf

private theorem involution_borelCellChart (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    involution (borelCellChart a b c t₁ t₂ t₃) =
      borelCellChart (b * t₃ / t₂) (a * t₂ / t₁) (c * t₃ / t₁) t₃ t₂ t₁ := by
  simp only [borelCellChart]
  rw [involution_mul, involution_unitriangular, involution_torus, torus_mul_unitriangular' h₂ h₁]
  all_goals ring_nf

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F] (g : Matrix (Fin 3) (Fin 3) F)

private theorem involution_mem_bigCell_iff : involution g ∈ bigCell ↔ g ∈ bigCell := by
  simp only [bigCell, Set.mem_setOf_eq, lowerLeftMinor1_involution, lowerLeftMinor2_involution, iff_self]

private theorem involution_preimage_bigCell :
    involution ⁻¹' (bigCell : Set (Matrix (Fin 3) (Fin 3) F)) = bigCell :=
  Set.ext fun g => involution_mem_bigCell_iff g

private theorem involution_mem_cycleCell123_iff : involution g ∈ cycleCell123 ↔ g ∈ cycleCell123 := by
  simp only [cycleCell123, Set.mem_setOf_eq, lowerLeftMinor1_involution, lowerLeftMinor2_involution, iff_self]

private theorem involution_preimage_cycleCell123 :
    involution ⁻¹' (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) = cycleCell123 :=
  Set.ext fun g => involution_mem_cycleCell123_iff g

private theorem involution_mem_cycleCell132_iff : involution g ∈ cycleCell132 ↔ g ∈ cycleCell132 := by
  simp only [cycleCell132, Set.mem_setOf_eq, lowerLeftMinor1_involution, lowerLeftMinor2_involution, iff_self]

private theorem involution_preimage_cycleCell132 :
    involution ⁻¹' (cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F)) = cycleCell132 :=
  Set.ext fun g => involution_mem_cycleCell132_iff g

private theorem involution_mem_reflCell12_iff : involution g ∈ reflCell12 ↔ g ∈ reflCell23 := by
  simp only [reflCell12, reflCell23, Set.mem_setOf_eq, lowerLeftMinor1_involution, involution_apply_one_zero,
      involution_apply_two_one, iff_self]

private theorem involution_preimage_reflCell12 :
    involution ⁻¹' (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) = reflCell23 :=
  Set.ext fun g => involution_mem_reflCell12_iff g

private theorem involution_mem_reflCell23_iff : involution g ∈ reflCell23 ↔ g ∈ reflCell12 := by
  simp only [reflCell23, reflCell12, Set.mem_setOf_eq, lowerLeftMinor1_involution, involution_apply_one_zero,
      involution_apply_two_one, iff_self]

private theorem involution_preimage_reflCell23 :
    involution ⁻¹' (reflCell23 : Set (Matrix (Fin 3) (Fin 3) F)) = reflCell12 :=
  Set.ext fun g => involution_mem_reflCell23_iff g

private theorem involution_mem_borelCell_iff : involution g ∈ borelCell ↔ g ∈ borelCell := by
  simp only [borelCell, Set.mem_setOf_eq, lowerLeftMinor1_involution, involution_apply_one_zero,
      involution_apply_two_one]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂, h₁⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₂, h₁⟩⟩

private theorem involution_preimage_borelCell :
    involution ⁻¹' (borelCell : Set (Matrix (Fin 3) (Fin 3) F)) = borelCell :=
  Set.ext fun g => involution_mem_borelCell_iff g

private theorem involution_preimage_stage_one :
    involution ⁻¹' (bigCell ∪ cycleCell123 ∪ cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F)) =
      bigCell ∪ cycleCell123 ∪ cycleCell132 := by
  simp only [Set.preimage_union, involution_preimage_bigCell, involution_preimage_cycleCell123,
    involution_preimage_cycleCell132]

private theorem involution_preimage_reflCells :
    involution ⁻¹' (reflCell12 ∪ reflCell23 : Set (Matrix (Fin 3) (Fin 3) F)) = reflCell12 ∪ reflCell23 := by
  simp only [Set.preimage_union, involution_preimage_reflCell12, involution_preimage_reflCell23]
  exact Set.union_comm _ _

private theorem involution_preimage_stage_two :
    involution ⁻¹'
        (bigCell ∪ cycleCell123 ∪ cycleCell132 ∪ (reflCell12 ∪ reflCell23) : Set (Matrix (Fin 3) (Fin 3) F)) =
      bigCell ∪ cycleCell123 ∪ cycleCell132 ∪ (reflCell12 ∪ reflCell23) := by
  rw [Set.preimage_union, involution_preimage_stage_one, involution_preimage_reflCells]

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

private theorem continuous_entry {R : Type*} [TopologicalSpace R] (i j : Fin 3) :
    Continuous fun g : Matrix (Fin 3) (Fin 3) R => g i j :=
  continuous_id.matrix_elem i j

variable {F : Type*} [Field F]

section Algebra

private theorem cycleCells_eq :
    (cycleCell123 ∪ cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F)) =
      (bigCell ∪ cycleCell123 ∪ cycleCell132) ∩ {g | lowerLeftMinor1 g = 0 ∨ lowerLeftMinor2 g = 0} := by
  ext g
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, mem_bigCell_iff, mem_cycleCell123_iff,
    mem_cycleCell132_iff]
  tauto

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

variable [TopologicalSpace F]

section FirstMinor

omit [Field F] in
private theorem continuous_lowerLeftMinor1 : Continuous (lowerLeftMinor1 : Matrix (Fin 3) (Fin 3) F → F) :=
  continuous_entry 2 0

end FirstMinor
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section EntryPieces

variable [T1Space F]

private theorem isOpen_lowerLeftMinor1_ne_zero : IsOpen {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g ≠ 0} :=
  isOpen_ne.preimage continuous_lowerLeftMinor1

private theorem isOpen_entry_ne_zero (i j : Fin 3) : IsOpen {g : Matrix (Fin 3) (Fin 3) F | g i j ≠ 0} :=
  isOpen_ne.preimage (continuous_entry i j)

private theorem isClosed_lowerLeftMinor1_eq_zero : IsClosed {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g = 0} :=
  isClosed_singleton.preimage continuous_lowerLeftMinor1

private theorem isClosed_entry_eq_zero (i j : Fin 3) : IsClosed {g : Matrix (Fin 3) (Fin 3) F | g i j = 0} :=
  isClosed_singleton.preimage (continuous_entry i j)

private theorem isClosed_borelCell : IsClosed (borelCell : Set (Matrix (Fin 3) (Fin 3) F)) :=
  (isClosed_entry_eq_zero 1 0).inter (isClosed_lowerLeftMinor1_eq_zero.inter (isClosed_entry_eq_zero 2 1))

private theorem isOpen_stage_two :
    IsOpen (bigCell ∪ cycleCell123 ∪ cycleCell132 ∪ (reflCell12 ∪ reflCell23) : Set (Matrix (Fin 3) (Fin 3) F)) := by
  rw [← compl_borelCell]
  exact isClosed_borelCell.isOpen_compl

end EntryPieces
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

variable [IsTopologicalRing F]

section Continuity

private theorem continuous_lowerLeftMinor2 : Continuous (lowerLeftMinor2 : Matrix (Fin 3) (Fin 3) F → F) :=
  ((continuous_entry 1 0).mul (continuous_entry 2 1)).sub ((continuous_entry 1 1).mul (continuous_entry 2 0))

private theorem continuous_bigCellChart :
    Continuous fun x : (F × F × F) × (F × F × F) × (F × F × F) =>
      bigCellChart x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [bigCellChart, unitriangular, torus, longestWeyl, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

private theorem continuous_cycleCell123Chart :
    Continuous fun x : (F × F × F) × (F × F × F) × (F × F) =>
      cycleCell123Chart x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [cycleCell123Chart, unitriangular, torus, cycle123, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

private theorem continuous_cycleCell132Chart :
    Continuous fun x : (F × F × F) × (F × F × F) × (F × F) =>
      cycleCell132Chart x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2.1 x.2.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [cycleCell132Chart, unitriangular, torus, cycle132, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

private theorem continuous_reflCell12Chart :
    Continuous fun x : (F × F × F) × (F × F × F) × F =>
      reflCell12Chart x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [reflCell12Chart, unitriangular, torus, refl12, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

private theorem continuous_reflCell23Chart :
    Continuous fun x : (F × F × F) × (F × F × F) × F =>
      reflCell23Chart x.1.1 x.1.2.1 x.1.2.2 x.2.1.1 x.2.1.2.1 x.2.1.2.2 x.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [reflCell23Chart, unitriangular, torus, refl23, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

private theorem continuous_borelCellChart :
    Continuous fun x : (F × F × F) × (F × F × F) =>
      borelCellChart x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2.1 x.2.2.2 :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [borelCellChart, unitriangular, torus, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> fun_prop

end Continuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Pieces

variable [T1Space F]

private theorem isOpen_lowerLeftMinor2_ne_zero : IsOpen {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor2 g ≠ 0} :=
  isOpen_ne.preimage continuous_lowerLeftMinor2

private theorem isClosed_lowerLeftMinor2_eq_zero : IsClosed {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor2 g = 0} :=
  isClosed_singleton.preimage continuous_lowerLeftMinor2

private theorem isOpen_bigCell : IsOpen (bigCell : Set (Matrix (Fin 3) (Fin 3) F)) :=
  isOpen_lowerLeftMinor1_ne_zero.inter isOpen_lowerLeftMinor2_ne_zero

private
theorem isOpen_stage_one : IsOpen (bigCell ∪ cycleCell123 ∪ cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F)) := by
  rw [bigCell_union_cycleCells]
  exact isOpen_lowerLeftMinor1_ne_zero.union isOpen_lowerLeftMinor2_ne_zero

private theorem isClosed_cycleCells_locus :
    IsClosed {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g = 0 ∨ lowerLeftMinor2 g = 0} :=
  isClosed_lowerLeftMinor1_eq_zero.union isClosed_lowerLeftMinor2_eq_zero

private theorem isClosed_reflCells_locus :
    IsClosed {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g = 0 ∧ lowerLeftMinor2 g = 0} :=
  isClosed_lowerLeftMinor1_eq_zero.inter isClosed_lowerLeftMinor2_eq_zero

end Pieces
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

private
theorem continuousOn_entry {R : Type*} [TopologicalSpace R] {s : Set (Matrix (Fin 3) (Fin 3) R)} (i j : Fin 3) :
    ContinuousOn (fun g : Matrix (Fin 3) (Fin 3) R => g i j) s :=
  (continuous_entry i j).continuousOn

variable {F : Type*} [Field F]

section Entries

variable (g : Matrix (Fin 3) (Fin 3) F)

private theorem cycleCell123_entries_ne_zero (hg : g ∈ cycleCell123) : g 1 0 ≠ 0 ∧ g 2 1 ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := hg
  rw [lowerLeftMinor2_of_lowerLeftMinor1_eq_zero g h₁] at h₂
  exact mul_ne_zero_iff.mp h₂

end Entries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuousOn_det {s : Set (Matrix (Fin 3) (Fin 3) F)} :
    ContinuousOn (fun g : Matrix (Fin 3) (Fin 3) F => g.det) s :=
  continuous_id.matrix_det.continuousOn

variable [ContinuousInv₀ F]

private theorem continuousOn_bigCellInverse :
    ContinuousOn (bigCellInverse (F := F)) (bigCell ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold bigCellInverse
  exact
    (((((continuousOn_entry 0 0).mul (continuousOn_entry 2 1)).sub ((continuousOn_entry 0 1).mul (continuousOn_entry 2
      0))).div₀ (continuous_lowerLeftMinor2.continuousOn) (fun g hg => hg.1.2)).prodMk
    (((continuousOn_entry 1 0).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    ((continuousOn_entry 0 0).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)))).prodMk
    ((((continuousOn_det).div₀ (continuous_lowerLeftMinor2.continuousOn) (fun g hg => hg.1.2)).prodMk
    ((((continuous_lowerLeftMinor2.continuousOn).neg).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    (continuousOn_entry 2 0))).prodMk
    (((continuousOn_entry 2 1).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    (((((continuousOn_entry 1 0).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul (continuousOn_entry 2
      0))).div₀ (continuous_lowerLeftMinor2.continuousOn) (fun g hg => hg.1.2)).prodMk
    ((continuousOn_entry 2 2).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)))))

private theorem continuousOn_cycleCell123Inverse :
    ContinuousOn (cycleCell123Inverse (F := F)) (cycleCell123 ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold cycleCell123Inverse
  exact
    (((continuousOn_entry 0 0).div₀ (continuousOn_entry 1 0) (fun g hg => (cycleCell123_entries_ne_zero g
      hg.1).1)).prodMk
    (((continuousOn_entry 1 1).div₀ (continuousOn_entry 2 1) (fun g hg => (cycleCell123_entries_ne_zero g
      hg.1).2)).prodMk
    ((continuousOn_entry 0 1).div₀ (continuousOn_entry 2 1) (fun g hg => (cycleCell123_entries_ne_zero g
      hg.1).2)))).prodMk
    ((((continuousOn_det).div₀ ((continuousOn_entry 1 0).mul (continuousOn_entry 2 1)) (fun g hg => mul_ne_zero
      (cycleCell123_entries_ne_zero g hg.1).1 (cycleCell123_entries_ne_zero g hg.1).2)).prodMk
    ((continuousOn_entry 1 0).prodMk
    (continuousOn_entry 2 1))).prodMk
    (((continuousOn_entry 2 2).div₀ (continuousOn_entry 2 1) (fun g hg => (cycleCell123_entries_ne_zero g
      hg.1).2)).prodMk
    (((((continuousOn_entry 1 1).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul (continuousOn_entry 2
      1))).neg).div₀ ((continuousOn_entry 1 0).mul (continuousOn_entry 2 1)) (fun g hg => mul_ne_zero
      (cycleCell123_entries_ne_zero g hg.1).1 (cycleCell123_entries_ne_zero g hg.1).2))))

private theorem continuousOn_cycleCell132Inverse :
    ContinuousOn (cycleCell132Inverse (F := F)) (cycleCell132 ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold cycleCell132Inverse
  exact
    (((((continuousOn_entry 0 0).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 0 2).mul (continuousOn_entry 2
      0))).div₀ (((continuousOn_entry 1 0).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul
      (continuousOn_entry 2 0))) (fun g hg => cycleCell132_denominator_ne_zero g hg.1 hg.2)).prodMk
    (((continuousOn_entry 1 0).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    ((continuousOn_entry 0 0).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)))).prodMk
    (((((((continuousOn_entry 0 0).mul (continuousOn_entry 2 1)).sub ((continuousOn_entry 0 1).mul (continuousOn_entry
      2 0))).neg).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    ((((((continuousOn_entry 1 0).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul (continuousOn_entry
      2 0))).neg).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    (continuousOn_entry 2 0))).prodMk
    (((continuousOn_entry 2 1).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1)).prodMk
    ((continuousOn_entry 2 2).div₀ (continuousOn_entry 2 0) (fun g hg => hg.1.1))))

private theorem continuousOn_reflCell12Inverse :
    ContinuousOn (reflCell12Inverse (F := F)) (reflCell12 ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold reflCell12Inverse
  exact
    (((continuousOn_entry 0 0).div₀ (continuousOn_entry 1 0) (fun g hg => hg.1.2.2)).prodMk
    (((continuousOn_entry 1 2).div₀ (continuousOn_entry 2 2) (fun g hg => reflCell12_apply_two_two_ne_zero g hg.1
      hg.2)).prodMk
    ((continuousOn_entry 0 2).div₀ (continuousOn_entry 2 2) (fun g hg => reflCell12_apply_two_two_ne_zero g hg.1
      hg.2)))).prodMk
    (((((((continuousOn_entry 0 0).mul (continuousOn_entry 1 1)).sub ((continuousOn_entry 0 1).mul (continuousOn_entry
      1 0))).neg).div₀ (continuousOn_entry 1 0) (fun g hg => hg.1.2.2)).prodMk
    ((continuousOn_entry 1 0).prodMk
    (continuousOn_entry 2 2))).prodMk
    ((continuousOn_entry 1 1).div₀ (continuousOn_entry 1 0) (fun g hg => hg.1.2.2)))

private theorem continuousOn_reflCell23Inverse :
    ContinuousOn (reflCell23Inverse (F := F)) (reflCell23 ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold reflCell23Inverse
  exact
    (((((continuousOn_entry 0 1).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 0 2).mul (continuousOn_entry 2
      1))).div₀ (((continuousOn_entry 1 1).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul
      (continuousOn_entry 2 1))) (fun g hg => reflCell23_denominator_ne_zero g hg.1 hg.2)).prodMk
    (((continuousOn_entry 1 1).div₀ (continuousOn_entry 2 1) (fun g hg => hg.1.2.2)).prodMk
    ((continuousOn_entry 0 1).div₀ (continuousOn_entry 2 1) (fun g hg => hg.1.2.2)))).prodMk
    (((continuousOn_entry 0 0).prodMk
    ((((((continuousOn_entry 1 1).mul (continuousOn_entry 2 2)).sub ((continuousOn_entry 1 2).mul (continuousOn_entry
      2 1))).neg).div₀ (continuousOn_entry 2 1) (fun g hg => hg.1.2.2)).prodMk
    (continuousOn_entry 2 1))).prodMk
    ((continuousOn_entry 2 2).div₀ (continuousOn_entry 2 1) (fun g hg => hg.1.2.2)))

private theorem continuousOn_borelCellInverse :
    ContinuousOn (borelCellInverse (F := F)) (borelCell ∩ {g | g.det ≠ 0} : Set (Matrix (Fin 3) (Fin 3) F)) := by
  unfold borelCellInverse
  exact
    (((continuousOn_entry 0 1).div₀ (continuousOn_entry 1 1) (fun g hg => borelCell_apply_one_one_ne_zero g hg.1
      hg.2)).prodMk
    (((continuousOn_entry 1 2).div₀ (continuousOn_entry 2 2) (fun g hg => borelCell_apply_two_two_ne_zero g hg.1
      hg.2)).prodMk
    ((continuousOn_entry 0 2).div₀ (continuousOn_entry 2 2) (fun g hg => borelCell_apply_two_two_ne_zero g hg.1
      hg.2)))).prodMk
    ((continuousOn_entry 0 0).prodMk
    ((continuousOn_entry 1 1).prodMk
    (continuousOn_entry 2 2)))

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

private def cycleCells : Set (Matrix (Fin 3) (Fin 3) F) := cycleCell123 ∪ cycleCell132

private def reflCells : Set (Matrix (Fin 3) (Fin 3) F) := reflCell12 ∪ reflCell23

private def stageOne : Set (Matrix (Fin 3) (Fin 3) F) := bigCell ∪ cycleCells

private def stageTwo : Set (Matrix (Fin 3) (Fin 3) F) := stageOne ∪ reflCells

private theorem stageOne_eq : (stageOne : Set (Matrix (Fin 3) (Fin 3) F)) = bigCell ∪ cycleCell123 ∪ cycleCell132 := by
  rw [stageOne, cycleCells, Set.union_assoc]

private theorem stageTwo_eq :
    (stageTwo : Set (Matrix (Fin 3) (Fin 3) F)) =
      bigCell ∪ cycleCell123 ∪ cycleCell132 ∪ (reflCell12 ∪ reflCell23) := by
  rw [stageTwo, stageOne_eq, reflCells]

private theorem isOpen_stageOne [TopologicalSpace F] [T1Space F] [IsTopologicalRing F] :
    IsOpen (stageOne : Set (Matrix (Fin 3) (Fin 3) F)) := by
  rw [stageOne_eq]
  exact isOpen_stage_one

private
theorem isOpen_stageTwo [TopologicalSpace F] [T1Space F] : IsOpen (stageTwo : Set (Matrix (Fin 3) (Fin 3) F)) := by
  rw [stageTwo_eq]
  exact isOpen_stage_two

private theorem stageOne_diff_bigCell : (stageOne : Set (Matrix (Fin 3) (Fin 3) F)) \ bigCell = cycleCells := by
  rw [stageOne_eq, bigCell_union_cycleCells, cycleCells]
  exact stage_two_eq F

private theorem stageTwo_diff_stageOne : (stageTwo : Set (Matrix (Fin 3) (Fin 3) F)) \ stageOne = reflCells := by
  rw [stageTwo, reflCells, reflCells_eq, stageOne_eq, bigCell_union_cycleCells]
  ext g
  simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not]
  tauto

private theorem compl_stageTwo : (stageTwo : Set (Matrix (Fin 3) (Fin 3) F))ᶜ = borelCell := by
  rw [stageTwo_eq, ← compl_borelCell, compl_compl]

private theorem cycleCells_diff_cycleCell123 :
    (cycleCells : Set (Matrix (Fin 3) (Fin 3) F)) \ cycleCell123 = cycleCell132 := by
  ext g
  simp only [cycleCells, Set.mem_diff, Set.mem_union, mem_cycleCell123_iff, mem_cycleCell132_iff]
  tauto

private
theorem reflCells_diff_reflCell12 : (reflCells : Set (Matrix (Fin 3) (Fin 3) F)) \ reflCell12 = reflCell23 := by
  ext g
  simp only [reflCells, Set.mem_diff, Set.mem_union, mem_reflCell12_iff, mem_reflCell23_iff]
  tauto

private theorem cycleCell123_eq_inter_closed' :
    (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) = cycleCells ∩ {g | lowerLeftMinor1 g = 0} :=
  cycleCell123_eq_inter_closed F

private theorem cycleCell123_eq_inter_open' :
    (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F)) = cycleCells ∩ {g | lowerLeftMinor2 g ≠ 0} :=
  cycleCell123_eq_inter_open F

private
theorem reflCell12_eq_inter_closed' : (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) = reflCells ∩ {g | g 2 1 = 0} :=
  reflCell12_eq_inter_closed F

private
theorem reflCell12_eq_inter_open' : (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F)) = reflCells ∩ {g | g 1 0 ≠ 0} :=
  reflCell12_eq_inter_open F

section Invariance

variable {x y z : F} {g : Matrix (Fin 3) (Fin 3) F}

private theorem unitriangular_mul_mem_bigCell (h : g ∈ bigCell) : unitriangular x y z * g ∈ bigCell := by
  rw [mem_bigCell_iff] at h ⊢
  rwa [lowerLeftMinor1_unitriangular_mul, lowerLeftMinor2_unitriangular_mul]

private theorem mul_unitriangular_mem_bigCell (h : g ∈ bigCell) : g * unitriangular x y z ∈ bigCell := by
  rw [mem_bigCell_iff] at h ⊢
  rwa [lowerLeftMinor1_mul_unitriangular, lowerLeftMinor2_mul_unitriangular]

private
theorem unitriangular_mul_mem_cycleCell123 (h : g ∈ cycleCell123) : unitriangular x y z * g ∈ cycleCell123 := by
  rw [mem_cycleCell123_iff] at h ⊢
  rwa [lowerLeftMinor1_unitriangular_mul, lowerLeftMinor2_unitriangular_mul]

private
theorem mul_unitriangular_mem_cycleCell123 (h : g ∈ cycleCell123) : g * unitriangular x y z ∈ cycleCell123 := by
  rw [mem_cycleCell123_iff] at h ⊢
  rwa [lowerLeftMinor1_mul_unitriangular, lowerLeftMinor2_mul_unitriangular]

private
theorem unitriangular_mul_mem_cycleCell132 (h : g ∈ cycleCell132) : unitriangular x y z * g ∈ cycleCell132 := by
  rw [mem_cycleCell132_iff] at h ⊢
  rwa [lowerLeftMinor1_unitriangular_mul, lowerLeftMinor2_unitriangular_mul]

private
theorem mul_unitriangular_mem_cycleCell132 (h : g ∈ cycleCell132) : g * unitriangular x y z ∈ cycleCell132 := by
  rw [mem_cycleCell132_iff] at h ⊢
  rwa [lowerLeftMinor1_mul_unitriangular, lowerLeftMinor2_mul_unitriangular]

private theorem unitriangular_mul_mem_reflCell12 (h : g ∈ reflCell12) : unitriangular x y z * g ∈ reflCell12 := by
  rw [mem_reflCell12_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.1
  rwa [lowerLeftMinor1_unitriangular_mul, unitriangular_mul_apply_two_one, unitriangular_mul_apply_one_zero, h₂₀,
    mul_zero, add_zero]

private theorem mul_unitriangular_mem_reflCell12 (h : g ∈ reflCell12) : g * unitriangular x y z ∈ reflCell12 := by
  rw [mem_reflCell12_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.1
  rwa [lowerLeftMinor1_mul_unitriangular, mul_unitriangular_apply_one_zero, mul_unitriangular_apply_two_one, h₂₀,
    zero_mul, add_zero]

private theorem unitriangular_mul_mem_reflCell23 (h : g ∈ reflCell23) : unitriangular x y z * g ∈ reflCell23 := by
  rw [mem_reflCell23_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.1
  rwa [lowerLeftMinor1_unitriangular_mul, unitriangular_mul_apply_two_one, unitriangular_mul_apply_one_zero, h₂₀,
    mul_zero, add_zero]

private theorem mul_unitriangular_mem_reflCell23 (h : g ∈ reflCell23) : g * unitriangular x y z ∈ reflCell23 := by
  rw [mem_reflCell23_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.1
  rwa [lowerLeftMinor1_mul_unitriangular, mul_unitriangular_apply_one_zero, mul_unitriangular_apply_two_one, h₂₀,
    zero_mul, add_zero]

private theorem unitriangular_mul_mem_borelCell (h : g ∈ borelCell) : unitriangular x y z * g ∈ borelCell := by
  rw [mem_borelCell_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.2.1
  rwa [lowerLeftMinor1_unitriangular_mul, unitriangular_mul_apply_two_one, unitriangular_mul_apply_one_zero, h₂₀,
    mul_zero, add_zero]

private theorem mul_unitriangular_mem_borelCell (h : g ∈ borelCell) : g * unitriangular x y z ∈ borelCell := by
  rw [mem_borelCell_iff] at h ⊢
  have h₂₀ : g 2 0 = 0 := h.2.1
  rwa [lowerLeftMinor1_mul_unitriangular, mul_unitriangular_apply_one_zero, mul_unitriangular_apply_two_one, h₂₀,
    zero_mul, add_zero]

private theorem unitriangular_mul_mem_cycleCells (h : g ∈ cycleCells) : unitriangular x y z * g ∈ cycleCells := by
  rcases h with h | h
  · exact Or.inl (unitriangular_mul_mem_cycleCell123 h)
  · exact Or.inr (unitriangular_mul_mem_cycleCell132 h)

private theorem unitriangular_mul_mem_reflCells (h : g ∈ reflCells) : unitriangular x y z * g ∈ reflCells := by
  rcases h with h | h
  · exact Or.inl (unitriangular_mul_mem_reflCell12 h)
  · exact Or.inr (unitriangular_mul_mem_reflCell23 h)

private theorem unitriangular_mul_mem_stageOne (h : g ∈ stageOne) : unitriangular x y z * g ∈ stageOne := by
  rcases h with h | h
  · exact Or.inl (unitriangular_mul_mem_bigCell h)
  · exact Or.inr (unitriangular_mul_mem_cycleCells h)

private theorem unitriangular_mul_mem_stageTwo (h : g ∈ stageTwo) : unitriangular x y z * g ∈ stageTwo := by
  rcases h with h | h
  · exact Or.inl (unitriangular_mul_mem_stageOne h)
  · exact Or.inr (unitriangular_mul_mem_reflCells h)

private theorem mul_unitriangular_mem_cycleCells (h : g ∈ cycleCells) : g * unitriangular x y z ∈ cycleCells := by
  rcases h with h | h
  · exact Or.inl (mul_unitriangular_mem_cycleCell123 h)
  · exact Or.inr (mul_unitriangular_mem_cycleCell132 h)

private theorem mul_unitriangular_mem_reflCells (h : g ∈ reflCells) : g * unitriangular x y z ∈ reflCells := by
  rcases h with h | h
  · exact Or.inl (mul_unitriangular_mem_reflCell12 h)
  · exact Or.inr (mul_unitriangular_mem_reflCell23 h)

private theorem mul_unitriangular_mem_stageOne (h : g ∈ stageOne) : g * unitriangular x y z ∈ stageOne := by
  rcases h with h | h
  · exact Or.inl (mul_unitriangular_mem_bigCell h)
  · exact Or.inr (mul_unitriangular_mem_cycleCells h)

private theorem mul_unitriangular_mem_stageTwo (h : g ∈ stageTwo) : g * unitriangular x y z ∈ stageTwo := by
  rcases h with h | h
  · exact Or.inl (mul_unitriangular_mem_stageOne h)
  · exact Or.inr (mul_unitriangular_mem_reflCells h)

end Invariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section GeneralLinear

private def bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (bigCell : Set (Matrix (Fin 3) (Fin 3) F))

private
def cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (cycleCell123 : Set (Matrix (Fin 3) (Fin 3) F))

private
def cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (cycleCell132 : Set (Matrix (Fin 3) (Fin 3) F))

private
def reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (reflCell12 : Set (Matrix (Fin 3) (Fin 3) F))

private
def reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (reflCell23 : Set (Matrix (Fin 3) (Fin 3) F))

private def borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (borelCell : Set (Matrix (Fin 3) (Fin 3) F))

private
def cycleCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (cycleCells : Set (Matrix (Fin 3) (Fin 3) F))

private def reflCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (reflCells : Set (Matrix (Fin 3) (Fin 3) F))

private def stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (stageOne : Set (Matrix (Fin 3) (Fin 3) F))

private def stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ := Units.val ⁻¹' (stageTwo : Set (Matrix (Fin 3) (Fin 3) F))

variable {u : (Matrix (Fin 3) (Fin 3) F)ˣ}

private theorem mem_bigCellGL : u ∈ bigCellGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ bigCell := Iff.rfl

private theorem mem_cycleCell123GL : u ∈ cycleCell123GL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ cycleCell123 := Iff.rfl

private theorem mem_cycleCell132GL : u ∈ cycleCell132GL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ cycleCell132 := Iff.rfl

private theorem mem_reflCell12GL : u ∈ reflCell12GL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ reflCell12 := Iff.rfl

private theorem mem_reflCell23GL : u ∈ reflCell23GL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ reflCell23 := Iff.rfl

private theorem mem_borelCellGL : u ∈ borelCellGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ borelCell := Iff.rfl

private theorem mem_cycleCellsGL : u ∈ cycleCellsGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ cycleCells := Iff.rfl

private theorem mem_reflCellsGL : u ∈ reflCellsGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ reflCells := Iff.rfl

private theorem mem_stageOneGL : u ∈ stageOneGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ stageOne := Iff.rfl

private theorem mem_stageTwoGL : u ∈ stageTwoGL ↔ (u : Matrix (Fin 3) (Fin 3) F) ∈ stageTwo := Iff.rfl

private
theorem cycleCellsGL_eq : (cycleCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = cycleCell123GL ∪ cycleCell132GL := by
  simp only [cycleCellsGL, cycleCell123GL, cycleCell132GL, cycleCells, Set.preimage_union]

private theorem reflCellsGL_eq : (reflCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = reflCell12GL ∪ reflCell23GL := by
  simp only [reflCellsGL, reflCell12GL, reflCell23GL, reflCells, Set.preimage_union]

private theorem stageOneGL_eq : (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = bigCellGL ∪ cycleCellsGL := by
  simp only [stageOneGL, bigCellGL, cycleCellsGL, stageOne, Set.preimage_union]

private theorem stageTwoGL_eq : (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageOneGL ∪ reflCellsGL := by
  simp only [stageTwoGL, stageOneGL, reflCellsGL, stageTwo, Set.preimage_union]

private theorem cycleCell123GL_subset : (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ cycleCellsGL := by
  rw [cycleCellsGL_eq]
  exact Set.subset_union_left

private theorem cycleCell132GL_subset : (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ cycleCellsGL := by
  rw [cycleCellsGL_eq]
  exact Set.subset_union_right

private theorem reflCell12GL_subset : (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ reflCellsGL := by
  rw [reflCellsGL_eq]
  exact Set.subset_union_left

private theorem reflCell23GL_subset : (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ reflCellsGL := by
  rw [reflCellsGL_eq]
  exact Set.subset_union_right

private theorem bigCellGL_subset : (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageOneGL := by
  rw [stageOneGL_eq]
  exact Set.subset_union_left

private theorem cycleCellsGL_subset : (cycleCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageOneGL := by
  rw [stageOneGL_eq]
  exact Set.subset_union_right

private theorem stageOneGL_subset : (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageTwoGL := by
  rw [stageTwoGL_eq]
  exact Set.subset_union_left

private theorem reflCellsGL_subset : (reflCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageTwoGL := by
  rw [stageTwoGL_eq]
  exact Set.subset_union_right

private theorem cycleCellsGL_eq_diff : (cycleCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageOneGL \ bigCellGL := by
  simp only [cycleCellsGL, stageOneGL, bigCellGL]
  rw [← Set.preimage_diff, stageOne_diff_bigCell]

private theorem reflCellsGL_eq_diff : (reflCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageTwoGL \ stageOneGL := by
  simp only [reflCellsGL, stageTwoGL, stageOneGL]
  rw [← Set.preimage_diff, stageTwo_diff_stageOne]

private theorem borelCellGL_eq_compl : (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageTwoGLᶜ := by
  simp only [borelCellGL, stageTwoGL]
  rw [← Set.preimage_compl, compl_stageTwo]

private theorem cycleCell123GL_eq_inter_closed :
    (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      cycleCellsGL ∩ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g = 0} := by
  simp only [cycleCell123GL, cycleCellsGL]
  rw [← Set.preimage_inter, ← cycleCell123_eq_inter_closed']

private theorem cycleCell123GL_eq_inter_open :
    (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      cycleCellsGL ∩ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor2 g ≠ 0} := by
  simp only [cycleCell123GL, cycleCellsGL]
  rw [← Set.preimage_inter, ← cycleCell123_eq_inter_open']

private theorem cycleCell132GL_eq_diff :
    (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = cycleCellsGL \ cycleCell123GL := by
  simp only [cycleCell132GL, cycleCellsGL, cycleCell123GL]
  rw [← Set.preimage_diff, cycleCells_diff_cycleCell123]

private theorem reflCell12GL_eq_inter_closed :
    (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      reflCellsGL ∩ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | g 2 1 = 0} := by
  simp only [reflCell12GL, reflCellsGL]
  rw [← Set.preimage_inter, ← reflCell12_eq_inter_closed']

private theorem reflCell12GL_eq_inter_open :
    (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      reflCellsGL ∩ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | g 1 0 ≠ 0} := by
  simp only [reflCell12GL, reflCellsGL]
  rw [← Set.preimage_inter, ← reflCell12_eq_inter_open']

private
theorem reflCell23GL_eq_diff : (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = reflCellsGL \ reflCell12GL := by
  simp only [reflCell23GL, reflCellsGL, reflCell12GL]
  rw [← Set.preimage_diff, reflCells_diff_reflCell12]

private theorem mul_mem_preimage_of_val_eq {C : Set (Matrix (Fin 3) (Fin 3) F)} {x y z : F}
    (hC : ∀ g ∈ C, unitriangular x y z * g ∈ C) {n u : (Matrix (Fin 3) (Fin 3) F)ˣ}
    (hn : (n : Matrix (Fin 3) (Fin 3) F) = unitriangular x y z) (hu : u ∈ Units.val ⁻¹' C) :
    n * u ∈ Units.val ⁻¹' C := by
  show ((n * u : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) ∈ C
  rw [Units.val_mul, hn]
  exact hC _ hu

private theorem mul_mem_preimage_of_val_eq' {C : Set (Matrix (Fin 3) (Fin 3) F)} {x y z : F}
    (hC : ∀ g ∈ C, g * unitriangular x y z ∈ C) {n u : (Matrix (Fin 3) (Fin 3) F)ˣ}
    (hn : (n : Matrix (Fin 3) (Fin 3) F) = unitriangular x y z) (hu : u ∈ Units.val ⁻¹' C) :
    u * n ∈ Units.val ⁻¹' C := by
  show ((u * n : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) ∈ C
  rw [Units.val_mul, hn]
  exact hC _ hu

end GeneralLinear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Topology

variable [TopologicalSpace F] [T1Space F] [IsTopologicalRing F]

private theorem isOpen_bigCellGL :
    IsOpen (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
  isOpen_bigCell.preimage Units.continuous_val

private theorem isOpen_stageOneGL :
    IsOpen (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
  isOpen_stageOne.preimage Units.continuous_val

omit [IsTopologicalRing F] in
private theorem isOpen_stageTwoGL :
    IsOpen (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
  isOpen_stageTwo.preimage Units.continuous_val

omit [IsTopologicalRing F] in
private theorem isClosed_borelCellGL : IsClosed (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
  isClosed_borelCell.preimage Units.continuous_val

omit [IsTopologicalRing F] in

private theorem isClosed_preimage_lowerLeftMinor1_eq_zero :
    IsClosed (Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor1 g = 0}) :=
  isClosed_lowerLeftMinor1_eq_zero.preimage Units.continuous_val

private theorem isOpen_preimage_lowerLeftMinor2_ne_zero :
    IsOpen (Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor2 g ≠ 0}) :=
  isOpen_lowerLeftMinor2_ne_zero.preimage Units.continuous_val

omit [IsTopologicalRing F] in

private theorem isClosed_preimage_entry_two_one_eq_zero :
    IsClosed (Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | g 2 1 = 0}) :=
  (isClosed_entry_eq_zero 2 1).preimage Units.continuous_val

omit [IsTopologicalRing F] in

private
theorem isOpen_preimage_entry_one_zero_ne_zero : IsOpen (Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | g 1 0 ≠ 0}) :=
  (isOpen_entry_ne_zero 1 0).preimage Units.continuous_val

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

open WhittakerCoinvariantsGL3

variable {F : Type*} [Field F]

private theorem rootGen12_mul_unitriangular_assoc (s a b c : F) (X : Matrix (Fin 3) (Fin 3) F) :
    rootGen12 s * (unitriangular a b c * X) = unitriangular (a + s) b (c + b * s) * X := by
  rw [← Matrix.mul_assoc, rootGen12_mul_unitriangular]

private theorem rootGen23_mul_unitriangular_assoc (s a b c : F) (X : Matrix (Fin 3) (Fin 3) F) :
    rootGen23 s * (unitriangular a b c * X) = unitriangular a (b + s) c * X := by
  rw [← Matrix.mul_assoc, rootGen23_mul_unitriangular]

private theorem rootGen13_mul_unitriangular_assoc (s a b c : F) (X : Matrix (Fin 3) (Fin 3) F) :
    rootGen13 s * (unitriangular a b c * X) = unitriangular a b (c + s) * X := by
  rw [← Matrix.mul_assoc, rootGen13_mul_unitriangular]

private theorem unitriangular_mul_rootGen12 (s p q r : F) :
    unitriangular p q r * rootGen12 s = unitriangular (p + s) q r := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen12_assoc (s p q r : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular p q r * (rootGen12 s * X) = unitriangular (p + s) q r * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen12]

private theorem unitriangular_mul_rootGen23 (s p q r : F) :
    unitriangular p q r * rootGen23 s = unitriangular p (q + s) (r + p * s) := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen23_assoc (s p q r : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular p q r * (rootGen23 s * X) = unitriangular p (q + s) (r + p * s) * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen23]

private theorem unitriangular_mul_rootGen13 (s p q r : F) :
    unitriangular p q r * rootGen13 s = unitriangular p q (r + s) := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mul_rootGen13_assoc (s p q r : F) (X : Matrix (Fin 3) (Fin 3) F) :
    unitriangular p q r * (rootGen13 s * X) = unitriangular p q (r + s) * X := by
  rw [← Matrix.mul_assoc, unitriangular_mul_rootGen13]

private theorem torus_mul_rootGen12 (t₁ t₂ t₃ : Fˣ) (s : F) :
    torus (t₁ : F) t₂ t₃ * rootGen12 s = rootGen12 (s * ((t₁ * t₂⁻¹ : Fˣ) : F)) * torus (t₁ : F) t₂ t₃ := by
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  simp only [unitriangular, torus, rootGen12, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.mul_fin_three, mul_zero,
    add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen12_assoc (t₁ t₂ t₃ : Fˣ) (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus (t₁ : F) t₂ t₃ * (rootGen12 s * X) =
      rootGen12 (s * ((t₁ * t₂⁻¹ : Fˣ) : F)) * (torus (t₁ : F) t₂ t₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen12, Matrix.mul_assoc]

private theorem torus_mul_rootGen23 (t₁ t₂ t₃ : Fˣ) (s : F) :
    torus (t₁ : F) t₂ t₃ * rootGen23 s = rootGen23 (s * ((t₂ * t₃⁻¹ : Fˣ) : F)) * torus (t₁ : F) t₂ t₃ := by
  have h₃ : (t₃ : F) ≠ 0 := t₃.ne_zero
  simp only [unitriangular, torus, rootGen23, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.mul_fin_three, mul_zero,
    add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen23_assoc (t₁ t₂ t₃ : Fˣ) (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus (t₁ : F) t₂ t₃ * (rootGen23 s * X) =
      rootGen23 (s * ((t₂ * t₃⁻¹ : Fˣ) : F)) * (torus (t₁ : F) t₂ t₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen23, Matrix.mul_assoc]

private theorem torus_mul_rootGen13 (t₁ t₂ t₃ : Fˣ) (s : F) :
    torus (t₁ : F) t₂ t₃ * rootGen13 s = rootGen13 (s * ((t₁ * t₃⁻¹ : Fˣ) : F)) * torus (t₁ : F) t₂ t₃ := by
  have h₃ : (t₃ : F) ≠ 0 := t₃.ne_zero
  simp only [unitriangular, torus, rootGen13, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.mul_fin_three, mul_zero,
    add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

private theorem torus_mul_rootGen13_assoc (t₁ t₂ t₃ : Fˣ) (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    torus (t₁ : F) t₂ t₃ * (rootGen13 s * X) =
      rootGen13 (s * ((t₁ * t₃⁻¹ : Fˣ) : F)) * (torus (t₁ : F) t₂ t₃ * X) := by
  rw [← Matrix.mul_assoc, torus_mul_rootGen13, Matrix.mul_assoc]

private theorem cycle123_mul_rootGen12 (s : F) :
    (cycle123 : Matrix (Fin 3) (Fin 3) F) * rootGen12 s = rootGen23 s * cycle123 := by
  simp only [unitriangular, rootGen12, rootGen23, cycle123, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem cycle123_mul_rootGen12_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (cycle123 : Matrix (Fin 3) (Fin 3) F) * (rootGen12 s * X) = rootGen23 s * (cycle123 * X) := by
  rw [← Matrix.mul_assoc, cycle123_mul_rootGen12, Matrix.mul_assoc]

private theorem cycle132_mul_rootGen23 (s : F) :
    (cycle132 : Matrix (Fin 3) (Fin 3) F) * rootGen23 s = rootGen12 s * cycle132 := by
  simp only [unitriangular, rootGen12, rootGen23, cycle132, Matrix.mul_fin_three, mul_zero, add_zero, mul_one,
    zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem cycle132_mul_rootGen23_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (cycle132 : Matrix (Fin 3) (Fin 3) F) * (rootGen23 s * X) = rootGen12 s * (cycle132 * X) := by
  rw [← Matrix.mul_assoc, cycle132_mul_rootGen23, Matrix.mul_assoc]

private theorem refl12_mul_rootGen23 (s : F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * rootGen23 s = rootGen13 s * refl12 := by
  simp only [unitriangular, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl12_mul_rootGen23_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * (rootGen23 s * X) = rootGen13 s * (refl12 * X) := by
  rw [← Matrix.mul_assoc, refl12_mul_rootGen23, Matrix.mul_assoc]

private theorem refl12_mul_rootGen13 (s : F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * rootGen13 s = rootGen23 s * refl12 := by
  simp only [unitriangular, rootGen23, rootGen13, refl12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl12_mul_rootGen13_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl12 : Matrix (Fin 3) (Fin 3) F) * (rootGen13 s * X) = rootGen23 s * (refl12 * X) := by
  rw [← Matrix.mul_assoc, refl12_mul_rootGen13, Matrix.mul_assoc]

private theorem refl23_mul_rootGen12 (s : F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * rootGen12 s = rootGen13 s * refl23 := by
  simp only [unitriangular, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl23_mul_rootGen12_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * (rootGen12 s * X) = rootGen13 s * (refl23 * X) := by
  rw [← Matrix.mul_assoc, refl23_mul_rootGen12, Matrix.mul_assoc]

private theorem refl23_mul_rootGen13 (s : F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * rootGen13 s = rootGen12 s * refl23 := by
  simp only [unitriangular, rootGen12, rootGen13, refl23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add,
    one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem refl23_mul_rootGen13_assoc (s : F) (X : Matrix (Fin 3) (Fin 3) F) :
    (refl23 : Matrix (Fin 3) (Fin 3) F) * (rootGen13 s * X) = rootGen12 s * (refl23 * X) := by
  rw [← Matrix.mul_assoc, refl23_mul_rootGen13, Matrix.mul_assoc]

private theorem unitriangular_zero_mul_rootGen12 (s q r : F) :
    unitriangular 0 q r * rootGen12 s = rootGen12 s * unitriangular 0 q (r - q * s) := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_mid_zero_mul_rootGen23 (s p r : F) :
    unitriangular p 0 r * rootGen23 s = rootGen23 s * unitriangular p 0 (r + p * s) := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_first_mul_rootGen23 (s p : F) :
    unitriangular p 0 0 * rootGen23 s = rootGen23 s * (rootGen13 (p * s) * unitriangular p 0 0) := by
  simp only [unitriangular, rootGen23, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_first_mul_rootGen13 (s p : F) :
    unitriangular p 0 0 * rootGen13 s = rootGen13 s * unitriangular p 0 0 := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_second_mul_rootGen12 (s q : F) :
    unitriangular 0 q 0 * rootGen12 s = rootGen12 s * (rootGen13 (-(q * s)) * unitriangular 0 q 0) := by
  simp only [unitriangular, rootGen12, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul,
    zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_second_mul_rootGen13 (s q : F) :
    unitriangular 0 q 0 * rootGen13 s = rootGen13 s * unitriangular 0 q 0 := by
  simp only [unitriangular, rootGen13, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen12_mul (x y z : F) :
    unitriangular x y z = rootGen12 x * unitriangular 0 y (z - y * x) := by
  simp only [unitriangular, rootGen12, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem unitriangular_eq_rootGen23_mul (x y z : F) :
    unitriangular x y z = rootGen23 y * unitriangular x 0 z := by
  simp only [unitriangular, rootGen23, Matrix.mul_fin_three, mul_zero, add_zero, mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> ring)

private theorem torus_mul_unitriangular (t₁ t₂ t₃ : Fˣ) (x y z : F) :
    torus (t₁ : F) t₂ t₃ * unitriangular x y z =
      unitriangular (x * ((t₁ * t₂⁻¹ : Fˣ) : F)) (y * ((t₂ * t₃⁻¹ : Fˣ) : F)) (z * ((t₁ * t₃⁻¹ : Fˣ) : F)) *
        torus (t₁ : F) t₂ t₃ := by
  have h₂ : (t₂ : F) ≠ 0 := t₂.ne_zero
  have h₃ : (t₃ : F) ≠ 0 := t₃.ne_zero
  simp only [unitriangular, torus, Units.val_mul, Units.val_inv_eq_inv_val, Matrix.mul_fin_three, mul_zero, add_zero,
    mul_one, zero_add, one_mul, zero_mul]
  all_goals (ext i j; fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
    Matrix.cons_val] <;> (try field_simp) <;> ring)

section BigCell

private def bigCellPoint : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ => bigCellChart a b c t₁ t₂ t₃ p q r

private theorem bigCellPoint_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (leftRoot12 s x.1, x.2) = rootGen12 s * bigCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, leftRoot12, bigCellChart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (leftRoot23 s x.1, x.2) = rootGen23 s * bigCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, leftRoot23, bigCellChart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (leftRoot13 s x.1, x.2) = rootGen13 s * bigCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, leftRoot13, bigCellChart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_bigCellRight12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (bigCellRight12 s x) = bigCellPoint x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, bigCellRight12, bigCellChart, Matrix.mul_assoc, unitriangular_mul_rootGen12, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_bigCellRight23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (bigCellRight23 s x) = bigCellPoint x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, bigCellRight23, bigCellChart, Matrix.mul_assoc, unitriangular_mul_rootGen23, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_bigCellRight13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (bigCellRight13 s x) = bigCellPoint x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, bigCellRight13, bigCellChart, Matrix.mul_assoc, unitriangular_mul_rootGen13, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem bigCellPoint_bigCellInvolution (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)) :
    bigCellPoint (bigCellInvolution x) = involution (bigCellPoint x) := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  simp only [bigCellPoint, bigCellInvolution, bigCellChart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_longestWeyl]
  simp only [Matrix.mul_assoc]

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell123

private def cycleCell123Point : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ => cycleCell123Chart a b c t₁ t₂ t₃ q r

private theorem cycleCell123Point_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (leftRoot12 s x.1, x.2) = rootGen12 s * cycleCell123Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, leftRoot12, cycleCell123Chart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (leftRoot23 s x.1, x.2) = rootGen23 s * cycleCell123Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, leftRoot23, cycleCell123Chart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (leftRoot13 s x.1, x.2) = rootGen13 s * cycleCell123Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, leftRoot13, cycleCell123Chart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_cycle123Right12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (cycle123Right12 s x) = cycleCell123Point x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, cycle123Right12, cycleCell123Chart, Matrix.mul_assoc, unitriangular_zero_mul_rootGen12,
    cycle123_mul_rootGen12_assoc, torus_mul_rootGen23_assoc, unitriangular_mul_rootGen23_assoc, zero_mul, mul_zero,
    zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_cycle123Right23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (cycle123Right23 s x) = cycleCell123Point x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, cycle123Right23, cycleCell123Chart, Matrix.mul_assoc, unitriangular_mul_rootGen23,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_cycle123Right13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (cycle123Right13 s x) = cycleCell123Point x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, cycle123Right13, cycleCell123Chart, Matrix.mul_assoc, unitriangular_mul_rootGen13,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell123Point_cycle123Involution (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell123Point (cycle123Involution x) = involution (cycleCell123Point x) := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  simp only [cycleCell123Point, cycle123Involution, cycleCell123Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_cycle123, unitriangular_eq_rootGen12_mul b a c]
  simp only [Matrix.mul_assoc, cycle123_mul_rootGen12_assoc, torus_mul_rootGen23_assoc,
    unitriangular_mul_rootGen23_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

end CycleCell123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell132

private def cycleCell132Point : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ => cycleCell132Chart a b c t₁ t₂ t₃ p r

private theorem cycleCell132Point_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (leftRoot12 s x.1, x.2) = rootGen12 s * cycleCell132Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, leftRoot12, cycleCell132Chart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (leftRoot23 s x.1, x.2) = rootGen23 s * cycleCell132Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, leftRoot23, cycleCell132Chart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (leftRoot13 s x.1, x.2) = rootGen13 s * cycleCell132Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, leftRoot13, cycleCell132Chart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_cycle132Right12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (cycle132Right12 s x) = cycleCell132Point x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, cycle132Right12, cycleCell132Chart, Matrix.mul_assoc, unitriangular_mul_rootGen12,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_cycle132Right23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (cycle132Right23 s x) = cycleCell132Point x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, cycle132Right23, cycleCell132Chart, Matrix.mul_assoc,
    unitriangular_mid_zero_mul_rootGen23, cycle132_mul_rootGen23_assoc, torus_mul_rootGen12_assoc,
    unitriangular_mul_rootGen12_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_cycle132Right13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (cycle132Right13 s x) = cycleCell132Point x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, cycle132Right13, cycleCell132Chart, Matrix.mul_assoc, unitriangular_mul_rootGen13,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem cycleCell132Point_cycle132Involution (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)) :
    cycleCell132Point (cycle132Involution x) = involution (cycleCell132Point x) := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  simp only [cycleCell132Point, cycle132Involution, cycleCell132Chart]
  rw [Matrix.mul_assoc (unitriangular a b c), involution_mul, involution_mul, involution_unitriangular,
    involution_unitriangular, involution_torus_mul_cycle132, unitriangular_eq_rootGen23_mul b a c]
  simp only [Matrix.mul_assoc, cycle132_mul_rootGen23_assoc, torus_mul_rootGen12_assoc,
    unitriangular_mul_rootGen12_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

end CycleCell132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell12

private def reflCell12Point : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ => reflCell12Chart a b c t₁ t₂ t₃ p

private theorem reflCell12Point_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (leftRoot12 s x.1, x.2) = rootGen12 s * reflCell12Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, leftRoot12, reflCell12Chart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell12Point_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (leftRoot23 s x.1, x.2) = rootGen23 s * reflCell12Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, leftRoot23, reflCell12Chart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell12Point_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (leftRoot13 s x.1, x.2) = rootGen13 s * reflCell12Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, leftRoot13, reflCell12Chart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell12Point_refl12Right12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (refl12Right12 s x) = reflCell12Point x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, refl12Right12, reflCell12Chart, Matrix.mul_assoc, unitriangular_mul_rootGen12, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell12Point_refl12Right23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (refl12Right23 s x) = reflCell12Point x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, refl12Right23, reflCell12Chart, Matrix.mul_assoc, unitriangular_first_mul_rootGen23,
    refl12_mul_rootGen23_assoc, refl12_mul_rootGen13_assoc, torus_mul_rootGen13_assoc, torus_mul_rootGen23_assoc,
    unitriangular_mul_rootGen13_assoc, unitriangular_mul_rootGen23_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell12Point_refl12Right13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell12Point (refl12Right13 s x) = reflCell12Point x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  simp only [reflCell12Point, refl12Right13, reflCell12Chart, Matrix.mul_assoc, unitriangular_first_mul_rootGen13,
    refl12_mul_rootGen13_assoc, torus_mul_rootGen23_assoc, unitriangular_mul_rootGen23_assoc, zero_mul, mul_zero,
    zero_add, add_zero]
  all_goals ring_nf

end ReflCell12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell23

private def reflCell23Point : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ => reflCell23Chart a b c t₁ t₂ t₃ q

private theorem reflCell23Point_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (leftRoot12 s x.1, x.2) = rootGen12 s * reflCell23Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, leftRoot12, reflCell23Chart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell23Point_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (leftRoot23 s x.1, x.2) = rootGen23 s * reflCell23Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, leftRoot23, reflCell23Chart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell23Point_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (leftRoot13 s x.1, x.2) = rootGen13 s * reflCell23Point x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, leftRoot13, reflCell23Chart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc,
    zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell23Point_refl23Right12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (refl23Right12 s x) = reflCell23Point x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, refl23Right12, reflCell23Chart, Matrix.mul_assoc, unitriangular_second_mul_rootGen12,
    refl23_mul_rootGen12_assoc, refl23_mul_rootGen13_assoc, torus_mul_rootGen13_assoc, torus_mul_rootGen12_assoc,
    unitriangular_mul_rootGen13_assoc, unitriangular_mul_rootGen12_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell23Point_refl23Right23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (refl23Right23 s x) = reflCell23Point x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, refl23Right23, reflCell23Chart, Matrix.mul_assoc, unitriangular_mul_rootGen23, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem reflCell23Point_refl23Right13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × F) :
    reflCell23Point (refl23Right13 s x) = reflCell23Point x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  simp only [reflCell23Point, refl23Right13, reflCell23Chart, Matrix.mul_assoc, unitriangular_second_mul_rootGen13,
    refl23_mul_rootGen13_assoc, torus_mul_rootGen12_assoc, unitriangular_mul_rootGen12_assoc, zero_mul, mul_zero,
    zero_add, add_zero]
  all_goals ring_nf

end ReflCell23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BorelCell

private def borelCellPoint : (F × F × F) × (Fˣ × Fˣ × Fˣ) → Matrix (Fin 3) (Fin 3) F :=
  fun ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ => borelCellChart a b c t₁ t₂ t₃

private theorem borelCellPoint_leftRoot12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (leftRoot12 s x.1, x.2) = rootGen12 s * borelCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, leftRoot12, borelCellChart, Matrix.mul_assoc, rootGen12_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_leftRoot23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (leftRoot23 s x.1, x.2) = rootGen23 s * borelCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, leftRoot23, borelCellChart, Matrix.mul_assoc, rootGen23_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_leftRoot13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (leftRoot13 s x.1, x.2) = rootGen13 s * borelCellPoint x := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, leftRoot13, borelCellChart, Matrix.mul_assoc, rootGen13_mul_unitriangular_assoc, zero_mul,
    mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_borelRight12 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (borelRight12 s x) = borelCellPoint x * rootGen12 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, borelRight12, borelCellChart, Matrix.mul_assoc, torus_mul_rootGen12,
    unitriangular_mul_rootGen12_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_borelRight23 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (borelRight23 s x) = borelCellPoint x * rootGen23 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, borelRight23, borelCellChart, Matrix.mul_assoc, torus_mul_rootGen23,
    unitriangular_mul_rootGen23_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_borelRight13 (s : F) (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (borelRight13 s x) = borelCellPoint x * rootGen13 s := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, borelRight13, borelCellChart, Matrix.mul_assoc, torus_mul_rootGen13,
    unitriangular_mul_rootGen13_assoc, zero_mul, mul_zero, zero_add, add_zero]
  all_goals ring_nf

private theorem borelCellPoint_borelInvolution (x : (F × F × F) × (Fˣ × Fˣ × Fˣ)) :
    borelCellPoint (borelInvolution x) = involution (borelCellPoint x) := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  simp only [borelCellPoint, borelInvolution, borelCellChart]
  rw [involution_mul, involution_unitriangular, involution_torus, torus_mul_unitriangular]

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

open WhittakerCoinvariantsGL3

variable {F : Type*} [Field F]

private theorem coe_mkOfDetNeZero {A : Matrix (Fin 3) (Fin 3) F} (h : A.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.mkOfDetNeZero A h : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = A :=
  rfl

section

variable [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]

private theorem continuous_mkOfDetNeZero {X : Type*} [TopologicalSpace X] {A : X → Matrix (Fin 3) (Fin 3) F}
    (hA : Continuous A) (h : ∀ x, (A x).det ≠ 0) :
    Continuous fun x => Matrix.GeneralLinearGroup.mkOfDetNeZero (A x) (h x) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa only [Function.comp_def, coe_mkOfDetNeZero] using hA
  · simp only [Matrix.coe_units_inv, coe_mkOfDetNeZero]
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hx : ContinuousAt Ring.inverse (A x).det := by
      have hinv : (Ring.inverse : F → F) = Inv.inv := Ring.inverse_eq_inv'
      rw [hinv]
      exact continuousAt_inv₀ (h x)
    exact (continuousAt_matrix_inv (A x) hx).comp' hA.continuousAt

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BigCell

private abbrev BigCellModel (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ) × (K × K × K)

private theorem det_bigCellPoint (x : BigCellModel F) : (bigCellPoint x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  show (bigCellChart a b c ↑t₁ ↑t₂ ↑t₃ p q r).det ≠ 0
  rw [det_bigCellChart]
  simp

private theorem bigCellPoint_mem (x : BigCellModel F) : bigCellPoint x ∈ bigCell := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  exact bigCellChart_mem a b c ↑t₁ ↑t₂ ↑t₃ p q r t₂.ne_zero t₃.ne_zero

private theorem bigCellPoint_eq :
    (bigCellPoint : BigCellModel F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      bigCellChart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1.1 ↑x.2.1.2.1 ↑x.2.1.2.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
  rfl

private def bigCellUnit (x : BigCellModel F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (bigCellPoint x) (det_bigCellPoint x)

@[scoped simp] private theorem bigCellUnit_val (x : BigCellModel F) :
    ((bigCellUnit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = bigCellPoint x := rfl

private theorem bigCell_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ bigCell) (hdet : g.det ≠ 0) :
    (bigCellInverse g).2.1.1 ≠ 0 ∧ (bigCellInverse g).2.1.2.1 ≠ 0 ∧ (bigCellInverse g).2.1.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (bigCellChart_bigCellInverse g hg)
  rw [det_bigCellChart] at h
  have h₃ : (bigCellInverse g).2.1.1 * (bigCellInverse g).2.1.2.1 * (bigCellInverse g).2.1.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def bigCellCoords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ bigCell) (hdet : g.det ≠ 0) :
    BigCellModel F :=
  let h := bigCell_slots_ne_zero g hg hdet
  ((bigCellInverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2),
    (bigCellInverse g).2.2)

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_bigCellPoint :
    Continuous (bigCellPoint : BigCellModel F → Matrix (Fin 3) (Fin 3) F) := by
  rw [bigCellPoint_eq]
  have hf : Continuous fun x : BigCellModel F =>
      (x.1, ((x.2.1.1 : F), (x.2.1.2.1 : F), (x.2.1.2.2 : F)), x.2.2) :=
    continuous_fst.prodMk (((Units.continuous_val.comp' continuous_snd.fst.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.fst.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.fst.snd.snd))).prodMk continuous_snd.snd)
  have h := continuous_bigCellChart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private def bigCellHomeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} ≃ₜ BigCellModel F where
  toFun g := bigCellCoords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨bigCellUnit x, bigCellPoint_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (bigCellChart_bigCellInverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, q, r⟩⟩ := x
    have h := bigCellInverse_bigCellChart a b c ↑t₁ ↑t₂ ↑t₃ p q r t₂.ne_zero t₃.ne_zero
    ext <;> simp [bigCellCoords, bigCellPoint, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} =>
        bigCellInverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_bigCellInverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} =>
      bigCell_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.fst, hinv.snd.fst.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.fst, hinv.snd.fst.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.snd, hinv.snd.fst.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk ((hu₁.prodMk (hu₂.prodMk hu₃)).prodMk hinv.snd.snd)
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_bigCellPoint det_bigCellPoint).subtype_mk bigCellPoint_mem

@[scoped simp] private theorem bigCellHomeomorph_symm_apply_val (x : BigCellModel F) :
    ((bigCellHomeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      bigCellUnit x := rfl

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell123

private abbrev CycleCell123Model (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ) × (K × K)

private theorem det_cycleCell123Point (x : CycleCell123Model F) : (cycleCell123Point x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  show (cycleCell123Chart a b c ↑t₁ ↑t₂ ↑t₃ q r).det ≠ 0
  rw [det_cycleCell123Chart]
  simp

private theorem cycleCell123Point_mem (x : CycleCell123Model F) : cycleCell123Point x ∈ cycleCell123 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  exact cycleCell123Chart_mem a b c ↑t₁ ↑t₂ ↑t₃ q r t₂.ne_zero t₃.ne_zero

private theorem cycleCell123Point_eq :
    (cycleCell123Point : CycleCell123Model F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      cycleCell123Chart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1.1 ↑x.2.1.2.1 ↑x.2.1.2.2 x.2.2.1 x.2.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
  rfl

private def cycleCell123Unit (x : CycleCell123Model F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (cycleCell123Point x) (det_cycleCell123Point x)

@[scoped simp] private theorem cycleCell123Unit_val (x : CycleCell123Model F) :
    ((cycleCell123Unit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = cycleCell123Point x := rfl

private theorem cycleCell123_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ cycleCell123) (hdet : g.det ≠ 0) :
    (cycleCell123Inverse g).2.1.1 ≠ 0 ∧ (cycleCell123Inverse g).2.1.2.1 ≠ 0 ∧ (cycleCell123Inverse g).2.1.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (cycleCell123Chart_cycleCell123Inverse g hg)
  rw [det_cycleCell123Chart] at h
  have h₃ : (cycleCell123Inverse g).2.1.1 * (cycleCell123Inverse g).2.1.2.1 * (cycleCell123Inverse g).2.1.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def cycleCell123Coords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ cycleCell123) (hdet : g.det ≠ 0) :
    CycleCell123Model F :=
  let h := cycleCell123_slots_ne_zero g hg hdet
  ((cycleCell123Inverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2),
    (cycleCell123Inverse g).2.2)

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_cycleCell123Point :
    Continuous (cycleCell123Point : CycleCell123Model F → Matrix (Fin 3) (Fin 3) F) := by
  rw [cycleCell123Point_eq]
  have hf : Continuous fun x : CycleCell123Model F =>
      (x.1, ((x.2.1.1 : F), (x.2.1.2.1 : F), (x.2.1.2.2 : F)), x.2.2) :=
    continuous_fst.prodMk (((Units.continuous_val.comp' continuous_snd.fst.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.fst.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.fst.snd.snd))).prodMk continuous_snd.snd)
  have h := continuous_cycleCell123Chart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private
def cycleCell123Homeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} ≃ₜ CycleCell123Model F where
  toFun g := cycleCell123Coords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨cycleCell123Unit x, cycleCell123Point_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (cycleCell123Chart_cycleCell123Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨q, r⟩⟩ := x
    have h := cycleCell123Inverse_cycleCell123Chart a b c ↑t₁ ↑t₂ ↑t₃ q r t₂.ne_zero t₃.ne_zero
    ext <;> simp [cycleCell123Coords, cycleCell123Point, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} =>
        cycleCell123Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_cycleCell123Inverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} =>
      cycleCell123_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.fst, hinv.snd.fst.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.fst, hinv.snd.fst.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.snd, hinv.snd.fst.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk ((hu₁.prodMk (hu₂.prodMk hu₃)).prodMk hinv.snd.snd)
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_cycleCell123Point det_cycleCell123Point).subtype_mk cycleCell123Point_mem

@[scoped simp] private theorem cycleCell123Homeomorph_symm_apply_val (x : CycleCell123Model F) :
    ((cycleCell123Homeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      cycleCell123Unit x := rfl

end CycleCell123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell132

private abbrev CycleCell132Model (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ) × (K × K)

private theorem det_cycleCell132Point (x : CycleCell132Model F) : (cycleCell132Point x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  show (cycleCell132Chart a b c ↑t₁ ↑t₂ ↑t₃ p r).det ≠ 0
  rw [det_cycleCell132Chart]
  simp

private theorem cycleCell132Point_mem (x : CycleCell132Model F) : cycleCell132Point x ∈ cycleCell132 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  exact cycleCell132Chart_mem a b c ↑t₁ ↑t₂ ↑t₃ p r t₃.ne_zero

private theorem cycleCell132Point_eq :
    (cycleCell132Point : CycleCell132Model F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      cycleCell132Chart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1.1 ↑x.2.1.2.1 ↑x.2.1.2.2 x.2.2.1 x.2.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
  rfl

private def cycleCell132Unit (x : CycleCell132Model F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (cycleCell132Point x) (det_cycleCell132Point x)

@[scoped simp] private theorem cycleCell132Unit_val (x : CycleCell132Model F) :
    ((cycleCell132Unit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = cycleCell132Point x := rfl

private theorem cycleCell132_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ cycleCell132) (hdet : g.det ≠ 0) :
    (cycleCell132Inverse g).2.1.1 ≠ 0 ∧ (cycleCell132Inverse g).2.1.2.1 ≠ 0 ∧ (cycleCell132Inverse g).2.1.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (cycleCell132Chart_cycleCell132Inverse g hg hdet)
  rw [det_cycleCell132Chart] at h
  have h₃ : (cycleCell132Inverse g).2.1.1 * (cycleCell132Inverse g).2.1.2.1 * (cycleCell132Inverse g).2.1.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def cycleCell132Coords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ cycleCell132) (hdet : g.det ≠ 0) :
    CycleCell132Model F :=
  let h := cycleCell132_slots_ne_zero g hg hdet
  ((cycleCell132Inverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2),
    (cycleCell132Inverse g).2.2)

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_cycleCell132Point :
    Continuous (cycleCell132Point : CycleCell132Model F → Matrix (Fin 3) (Fin 3) F) := by
  rw [cycleCell132Point_eq]
  have hf : Continuous fun x : CycleCell132Model F =>
      (x.1, ((x.2.1.1 : F), (x.2.1.2.1 : F), (x.2.1.2.2 : F)), x.2.2) :=
    continuous_fst.prodMk (((Units.continuous_val.comp' continuous_snd.fst.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.fst.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.fst.snd.snd))).prodMk continuous_snd.snd)
  have h := continuous_cycleCell132Chart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private
def cycleCell132Homeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} ≃ₜ CycleCell132Model F where
  toFun g := cycleCell132Coords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨cycleCell132Unit x, cycleCell132Point_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (cycleCell132Chart_cycleCell132Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2
      (Matrix.isUnits_det_units g.1).ne_zero))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, ⟨p, r⟩⟩ := x
    have h := cycleCell132Inverse_cycleCell132Chart a b c ↑t₁ ↑t₂ ↑t₃ p r t₂.ne_zero t₃.ne_zero
    ext <;> simp [cycleCell132Coords, cycleCell132Point, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} =>
        cycleCell132Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_cycleCell132Inverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} =>
      cycleCell132_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.fst, hinv.snd.fst.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.fst, hinv.snd.fst.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.snd, hinv.snd.fst.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk ((hu₁.prodMk (hu₂.prodMk hu₃)).prodMk hinv.snd.snd)
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_cycleCell132Point det_cycleCell132Point).subtype_mk cycleCell132Point_mem

@[scoped simp] private theorem cycleCell132Homeomorph_symm_apply_val (x : CycleCell132Model F) :
    ((cycleCell132Homeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      cycleCell132Unit x := rfl

end CycleCell132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell12

private abbrev ReflCell12Model (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ) × K

private theorem det_reflCell12Point (x : ReflCell12Model F) : (reflCell12Point x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  show (reflCell12Chart a b c ↑t₁ ↑t₂ ↑t₃ p).det ≠ 0
  rw [det_reflCell12Chart]
  simp

private theorem reflCell12Point_mem (x : ReflCell12Model F) : reflCell12Point x ∈ reflCell12 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  exact reflCell12Chart_mem a b c ↑t₁ ↑t₂ ↑t₃ p t₂.ne_zero

private theorem reflCell12Point_eq :
    (reflCell12Point : ReflCell12Model F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      reflCell12Chart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1.1 ↑x.2.1.2.1 ↑x.2.1.2.2 x.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
  rfl

private def reflCell12Unit (x : ReflCell12Model F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (reflCell12Point x) (det_reflCell12Point x)

@[scoped simp] private theorem reflCell12Unit_val (x : ReflCell12Model F) :
    ((reflCell12Unit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = reflCell12Point x := rfl

private theorem reflCell12_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ reflCell12) (hdet : g.det ≠ 0) :
    (reflCell12Inverse g).2.1.1 ≠ 0 ∧ (reflCell12Inverse g).2.1.2.1 ≠ 0 ∧ (reflCell12Inverse g).2.1.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (reflCell12Chart_reflCell12Inverse g hg hdet)
  rw [det_reflCell12Chart] at h
  have h₃ : (reflCell12Inverse g).2.1.1 * (reflCell12Inverse g).2.1.2.1 * (reflCell12Inverse g).2.1.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def reflCell12Coords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ reflCell12) (hdet : g.det ≠ 0) :
    ReflCell12Model F :=
  let h := reflCell12_slots_ne_zero g hg hdet
  ((reflCell12Inverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2),
    (reflCell12Inverse g).2.2)

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_reflCell12Point :
    Continuous (reflCell12Point : ReflCell12Model F → Matrix (Fin 3) (Fin 3) F) := by
  rw [reflCell12Point_eq]
  have hf : Continuous fun x : ReflCell12Model F =>
      (x.1, ((x.2.1.1 : F), (x.2.1.2.1 : F), (x.2.1.2.2 : F)), x.2.2) :=
    continuous_fst.prodMk (((Units.continuous_val.comp' continuous_snd.fst.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.fst.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.fst.snd.snd))).prodMk continuous_snd.snd)
  have h := continuous_reflCell12Chart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private def reflCell12Homeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} ≃ₜ ReflCell12Model F where
  toFun g := reflCell12Coords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨reflCell12Unit x, reflCell12Point_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (reflCell12Chart_reflCell12Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2
      (Matrix.isUnits_det_units g.1).ne_zero))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, p⟩ := x
    have h := reflCell12Inverse_reflCell12Chart a b c ↑t₁ ↑t₂ ↑t₃ p t₂.ne_zero t₃.ne_zero
    ext <;> simp [reflCell12Coords, reflCell12Point, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} =>
        reflCell12Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_reflCell12Inverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} =>
      reflCell12_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.fst, hinv.snd.fst.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.fst, hinv.snd.fst.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.snd, hinv.snd.fst.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk ((hu₁.prodMk (hu₂.prodMk hu₃)).prodMk hinv.snd.snd)
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_reflCell12Point det_reflCell12Point).subtype_mk reflCell12Point_mem

@[scoped simp] private theorem reflCell12Homeomorph_symm_apply_val (x : ReflCell12Model F) :
    ((reflCell12Homeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      reflCell12Unit x := rfl

end ReflCell12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell23

private abbrev ReflCell23Model (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ) × K

private theorem det_reflCell23Point (x : ReflCell23Model F) : (reflCell23Point x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  show (reflCell23Chart a b c ↑t₁ ↑t₂ ↑t₃ q).det ≠ 0
  rw [det_reflCell23Chart]
  simp

private theorem reflCell23Point_mem (x : ReflCell23Model F) : reflCell23Point x ∈ reflCell23 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  exact reflCell23Chart_mem a b c ↑t₁ ↑t₂ ↑t₃ q t₃.ne_zero

private theorem reflCell23Point_eq :
    (reflCell23Point : ReflCell23Model F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      reflCell23Chart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1.1 ↑x.2.1.2.1 ↑x.2.1.2.2 x.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
  rfl

private def reflCell23Unit (x : ReflCell23Model F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (reflCell23Point x) (det_reflCell23Point x)

@[scoped simp] private theorem reflCell23Unit_val (x : ReflCell23Model F) :
    ((reflCell23Unit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = reflCell23Point x := rfl

private theorem reflCell23_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ reflCell23) (hdet : g.det ≠ 0) :
    (reflCell23Inverse g).2.1.1 ≠ 0 ∧ (reflCell23Inverse g).2.1.2.1 ≠ 0 ∧ (reflCell23Inverse g).2.1.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (reflCell23Chart_reflCell23Inverse g hg hdet)
  rw [det_reflCell23Chart] at h
  have h₃ : (reflCell23Inverse g).2.1.1 * (reflCell23Inverse g).2.1.2.1 * (reflCell23Inverse g).2.1.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def reflCell23Coords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ reflCell23) (hdet : g.det ≠ 0) :
    ReflCell23Model F :=
  let h := reflCell23_slots_ne_zero g hg hdet
  ((reflCell23Inverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2),
    (reflCell23Inverse g).2.2)

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_reflCell23Point :
    Continuous (reflCell23Point : ReflCell23Model F → Matrix (Fin 3) (Fin 3) F) := by
  rw [reflCell23Point_eq]
  have hf : Continuous fun x : ReflCell23Model F =>
      (x.1, ((x.2.1.1 : F), (x.2.1.2.1 : F), (x.2.1.2.2 : F)), x.2.2) :=
    continuous_fst.prodMk (((Units.continuous_val.comp' continuous_snd.fst.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.fst.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.fst.snd.snd))).prodMk continuous_snd.snd)
  have h := continuous_reflCell23Chart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private def reflCell23Homeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} ≃ₜ ReflCell23Model F where
  toFun g := reflCell23Coords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨reflCell23Unit x, reflCell23Point_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (reflCell23Chart_reflCell23Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2
      (Matrix.isUnits_det_units g.1).ne_zero))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩, q⟩ := x
    have h := reflCell23Inverse_reflCell23Chart a b c ↑t₁ ↑t₂ ↑t₃ q t₂.ne_zero t₃.ne_zero
    ext <;> simp [reflCell23Coords, reflCell23Point, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} =>
        reflCell23Inverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_reflCell23Inverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} =>
      reflCell23_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.fst, hinv.snd.fst.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.fst, hinv.snd.fst.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst.snd.snd, hinv.snd.fst.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk ((hu₁.prodMk (hu₂.prodMk hu₃)).prodMk hinv.snd.snd)
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_reflCell23Point det_reflCell23Point).subtype_mk reflCell23Point_mem

@[scoped simp] private theorem reflCell23Homeomorph_symm_apply_val (x : ReflCell23Model F) :
    ((reflCell23Homeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      reflCell23Unit x := rfl

end ReflCell23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BorelCell

private abbrev BorelCellModel (K : Type*) [Field K] : Type _ := (K × K × K) × (Kˣ × Kˣ × Kˣ)

private theorem det_borelCellPoint (x : BorelCellModel F) : (borelCellPoint x).det ≠ 0 := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  show (borelCellChart a b c ↑t₁ ↑t₂ ↑t₃).det ≠ 0
  rw [det_borelCellChart]
  simp

private theorem borelCellPoint_mem (x : BorelCellModel F) : borelCellPoint x ∈ borelCell := by
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  exact borelCellChart_mem a b c ↑t₁ ↑t₂ ↑t₃

private theorem borelCellPoint_eq :
    (borelCellPoint : BorelCellModel F → Matrix (Fin 3) (Fin 3) F) = fun x =>
      borelCellChart x.1.1 x.1.2.1 x.1.2.2 ↑x.2.1 ↑x.2.2.1 ↑x.2.2.2 := by
  funext x
  obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
  rfl

private def borelCellUnit (x : BorelCellModel F) : (Matrix (Fin 3) (Fin 3) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borelCellPoint x) (det_borelCellPoint x)

@[scoped simp] private theorem borelCellUnit_val (x : BorelCellModel F) :
    ((borelCellUnit x : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = borelCellPoint x := rfl

private theorem borelCell_slots_ne_zero (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ borelCell) (hdet : g.det ≠ 0) :
    (borelCellInverse g).2.1 ≠ 0 ∧ (borelCellInverse g).2.2.1 ≠ 0 ∧ (borelCellInverse g).2.2.2 ≠ 0 := by
  have h := congrArg Matrix.det (borelCellChart_borelCellInverse g hg hdet)
  rw [det_borelCellChart] at h
  have h₃ : (borelCellInverse g).2.1 * (borelCellInverse g).2.2.1 * (borelCellInverse g).2.2.2 ≠ 0 :=
    fun h₀ => hdet (by simp [← h, h₀])
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).1, (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h₃).1).2,
    (mul_ne_zero_iff.mp h₃).2⟩

private def borelCellCoords (g : Matrix (Fin 3) (Fin 3) F) (hg : g ∈ borelCell) (hdet : g.det ≠ 0) :
    BorelCellModel F :=
  let h := borelCell_slots_ne_zero g hg hdet
  ((borelCellInverse g).1, (Units.mk0 _ h.1, Units.mk0 _ h.2.1, Units.mk0 _ h.2.2))

variable [TopologicalSpace F] [IsTopologicalRing F]

private theorem continuous_borelCellPoint :
    Continuous (borelCellPoint : BorelCellModel F → Matrix (Fin 3) (Fin 3) F) := by
  rw [borelCellPoint_eq]
  have hf : Continuous fun x : BorelCellModel F => (x.1, ((x.2.1 : F), (x.2.2.1 : F), (x.2.2.2 : F))) :=
    continuous_fst.prodMk ((Units.continuous_val.comp' continuous_snd.fst).prodMk
      ((Units.continuous_val.comp' continuous_snd.snd.fst).prodMk
        (Units.continuous_val.comp' continuous_snd.snd.snd)))
  have h := continuous_borelCellChart.comp' hf
  exact h

variable [ContinuousInv₀ F]

private def borelCellHomeomorph : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} ≃ₜ BorelCellModel F where
  toFun g := borelCellCoords (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
  invFun x := ⟨borelCellUnit x, borelCellPoint_mem x⟩
  left_inv g :=
    Subtype.ext (Units.ext (borelCellChart_borelCellInverse (g.1 : Matrix (Fin 3) (Fin 3) F) g.2
      (Matrix.isUnits_det_units g.1).ne_zero))
  right_inv x := by
    obtain ⟨⟨a, b, c⟩, ⟨t₁, t₂, t₃⟩⟩ := x
    have h := borelCellInverse_borelCellChart a b c ↑t₁ ↑t₂ ↑t₃ t₂.ne_zero t₃.ne_zero
    ext <;> simp [borelCellCoords, borelCellPoint, h]
  continuous_toFun := by
    have hval : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} =>
        (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} =>
        borelCellInverse (g.1 : Matrix (Fin 3) (Fin 3) F) :=
      continuousOn_borelCellInverse.comp_continuous hval fun g => ⟨g.2, (Matrix.isUnits_det_units g.1).ne_zero⟩
    have hne := fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} =>
      borelCell_slots_ne_zero (g.1 : Matrix (Fin 3) (Fin 3) F) g.2 (Matrix.isUnits_det_units g.1).ne_zero
    have hu₁ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} => Units.mk0 _ (hne g).1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.fst, hinv.snd.fst.inv₀ fun g => (hne g).1⟩
    have hu₂ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} => Units.mk0 _ (hne g).2.1 :=
      Units.continuous_iff.mpr ⟨hinv.snd.snd.fst, hinv.snd.snd.fst.inv₀ fun g => (hne g).2.1⟩
    have hu₃ : Continuous fun g : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} => Units.mk0 _ (hne g).2.2 :=
      Units.continuous_iff.mpr ⟨hinv.snd.snd.snd, hinv.snd.snd.snd.inv₀ fun g => (hne g).2.2⟩
    exact hinv.fst.prodMk (hu₁.prodMk (hu₂.prodMk hu₃))
  continuous_invFun :=
    (continuous_mkOfDetNeZero continuous_borelCellPoint det_borelCellPoint).subtype_mk borelCellPoint_mem

@[scoped simp] private theorem borelCellHomeomorph_symm_apply_val (x : BorelCellModel F) :
    ((borelCellHomeomorph.symm x : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL}) :
        (Matrix (Fin 3) (Fin 3) F)ˣ) =
      borelCellUnit x := rfl

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

private theorem involution_one : involution (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [involution, Matrix.transpose_one, mul_one, longestWeyl_mul_longestWeyl]

section Units

private def involutionUnit (g : (Matrix (Fin 3) (Fin 3) F)ˣ) : (Matrix (Fin 3) (Fin 3) F)ˣ where
  val := involution (g : Matrix (Fin 3) (Fin 3) F)
  inv := involution ((g⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F)
  val_inv := by rw [← involution_mul, Units.inv_mul, involution_one]
  inv_val := by rw [← involution_mul, Units.mul_inv, involution_one]

variable (u : (Matrix (Fin 3) (Fin 3) F)ˣ)

@[scoped simp] private theorem involutionUnit_val :
    ((involutionUnit u : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      involution (u : Matrix (Fin 3) (Fin 3) F) :=
  rfl

@[scoped simp] private theorem involutionUnit_inv_val :
    (((involutionUnit u)⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      involution ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) := rfl

private theorem involutionUnit_involutionUnit : involutionUnit (involutionUnit u) = u :=
  Units.ext (involution_involution (u : Matrix (Fin 3) (Fin 3) F))

private theorem involutionUnit_injective :
    Function.Injective (involutionUnit : (Matrix (Fin 3) (Fin 3) F)ˣ → (Matrix (Fin 3) (Fin 3) F)ˣ) :=
  fun a b h => by
  rw [← involutionUnit_involutionUnit a, h, involutionUnit_involutionUnit]

private theorem involutionUnit_preimage_of_preimage {C D : Set (Matrix (Fin 3) (Fin 3) F)} (h : involution ⁻¹' C = D) :
    involutionUnit ⁻¹' (Units.val ⁻¹' C : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = Units.val ⁻¹' D := by
  subst h
  exact Set.ext fun _ => Iff.rfl

end Units
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Sets

private theorem involution_preimage_cycleCells :
    involution ⁻¹' (cycleCells : Set (Matrix (Fin 3) (Fin 3) F)) = cycleCells := by
  simp only [cycleCells, Set.preimage_union, involution_preimage_cycleCell123,
    involution_preimage_cycleCell132]

private
theorem involution_preimage_reflCells' : involution ⁻¹' (reflCells : Set (Matrix (Fin 3) (Fin 3) F)) = reflCells := by
  rw [reflCells]
  exact involution_preimage_reflCells

private
theorem involution_preimage_stageOne : involution ⁻¹' (stageOne : Set (Matrix (Fin 3) (Fin 3) F)) = stageOne := by
  rw [stageOne_eq]
  exact involution_preimage_stage_one

private
theorem involution_preimage_stageTwo : involution ⁻¹' (stageTwo : Set (Matrix (Fin 3) (Fin 3) F)) = stageTwo := by
  rw [stageTwo_eq]
  exact involution_preimage_stage_two

private theorem involutionUnit_preimage_bigCellGL :
    involutionUnit ⁻¹' (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = bigCellGL :=
  involutionUnit_preimage_of_preimage involution_preimage_bigCell

private theorem involutionUnit_preimage_cycleCell123GL :
    involutionUnit ⁻¹' (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = cycleCell123GL :=
  involutionUnit_preimage_of_preimage involution_preimage_cycleCell123

private theorem involutionUnit_preimage_cycleCell132GL :
    involutionUnit ⁻¹' (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = cycleCell132GL :=
  involutionUnit_preimage_of_preimage involution_preimage_cycleCell132

private theorem involutionUnit_preimage_reflCell12GL :
    involutionUnit ⁻¹' (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = reflCell23GL :=
  involutionUnit_preimage_of_preimage involution_preimage_reflCell12

private theorem involutionUnit_preimage_reflCell23GL :
    involutionUnit ⁻¹' (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = reflCell12GL :=
  involutionUnit_preimage_of_preimage involution_preimage_reflCell23

private theorem involutionUnit_preimage_borelCellGL :
    involutionUnit ⁻¹' (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = borelCellGL :=
  involutionUnit_preimage_of_preimage involution_preimage_borelCell

private theorem involutionUnit_preimage_cycleCellsGL :
    involutionUnit ⁻¹' (cycleCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = cycleCellsGL :=
  involutionUnit_preimage_of_preimage involution_preimage_cycleCells

private theorem involutionUnit_preimage_reflCellsGL :
    involutionUnit ⁻¹' (reflCellsGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = reflCellsGL :=
  involutionUnit_preimage_of_preimage involution_preimage_reflCells'

private theorem involutionUnit_preimage_stageOneGL :
    involutionUnit ⁻¹' (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageOneGL :=
  involutionUnit_preimage_of_preimage involution_preimage_stageOne

private theorem involutionUnit_preimage_stageTwoGL :
    involutionUnit ⁻¹' (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageTwoGL :=
  involutionUnit_preimage_of_preimage involution_preimage_stageTwo

private theorem mem_iff_of_preimage_eq {α : Type*} {f : α → α} {S : Set α} (h : f ⁻¹' S = S) (u : α) :
    u ∈ S ↔ f u ∈ S :=
  (Set.ext_iff.mp h u).symm

private theorem mem_union_iff_of_mem_iff {α : Type*} {f : α → α} {S T : Set α} (hS : ∀ u, u ∈ S ↔ f u ∈ S)
    (hT : ∀ u, u ∈ T ↔ f u ∈ T) (u : α) : u ∈ S ∪ T ↔ f u ∈ S ∪ T := by
  simp only [Set.mem_union]
  exact or_congr (hS u) (hT u)

variable (u : (Matrix (Fin 3) (Fin 3) F)ˣ)

private theorem mem_bigCellGL_iff_involutionUnit : u ∈ bigCellGL ↔ involutionUnit u ∈ bigCellGL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_bigCellGL u

private theorem mem_cycleCell123GL_iff_involutionUnit : u ∈ cycleCell123GL ↔ involutionUnit u ∈ cycleCell123GL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_cycleCell123GL u

private theorem mem_cycleCell132GL_iff_involutionUnit : u ∈ cycleCell132GL ↔ involutionUnit u ∈ cycleCell132GL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_cycleCell132GL u

private theorem mem_borelCellGL_iff_involutionUnit : u ∈ borelCellGL ↔ involutionUnit u ∈ borelCellGL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_borelCellGL u

private theorem mem_stageOneGL_iff_involutionUnit : u ∈ stageOneGL ↔ involutionUnit u ∈ stageOneGL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_stageOneGL u

private theorem mem_stageTwoGL_iff_involutionUnit : u ∈ stageTwoGL ↔ involutionUnit u ∈ stageTwoGL :=
  mem_iff_of_preimage_eq involutionUnit_preimage_stageTwoGL u

private theorem mem_bigCellGL_union_cycleCell123GL_iff_involutionUnit :
    u ∈ bigCellGL ∪ cycleCell123GL ↔ involutionUnit u ∈ bigCellGL ∪ cycleCell123GL :=
  mem_union_iff_of_mem_iff mem_bigCellGL_iff_involutionUnit mem_cycleCell123GL_iff_involutionUnit u

end Sets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

private
theorem continuous_involution : Continuous (involution : Matrix (Fin 3) (Fin 3) F → Matrix (Fin 3) (Fin 3) F) := by
  show Continuous fun g : Matrix (Fin 3) (Fin 3) F =>
    longestWeyl * g.transpose * longestWeyl
  exact (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const

private theorem continuous_involutionUnit :
    Continuous (involutionUnit : (Matrix (Fin 3) (Fin 3) F)ˣ → (Matrix (Fin 3) (Fin 3) F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_involution.comp Units.continuous_val
  · exact continuous_involution.comp Units.continuous_coe_inv

private def involutionHomeomorph : (Matrix (Fin 3) (Fin 3) F)ˣ ≃ₜ (Matrix (Fin 3) (Fin 3) F)ˣ where
  toFun := involutionUnit
  invFun := involutionUnit
  left_inv := involutionUnit_involutionUnit
  right_inv := involutionUnit_involutionUnit
  continuous_toFun := continuous_involutionUnit
  continuous_invFun := continuous_involutionUnit

@[scoped simp] private theorem involutionHomeomorph_apply (u : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    involutionHomeomorph u = involutionUnit u :=
  rfl

@[scoped simp] private theorem val_involutionHomeomorph_apply (u : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((involutionHomeomorph u : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      involution (u : Matrix (Fin 3) (Fin 3) F) := rfl

private theorem involutionHomeomorph_involutionHomeomorph (u : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    involutionHomeomorph (involutionHomeomorph u) = u :=
  involutionUnit_involutionUnit u

@[scoped simp] private theorem involutionHomeomorph_symm :
    (involutionHomeomorph : (Matrix (Fin 3) (Fin 3) F)ˣ ≃ₜ (Matrix (Fin 3) (Fin 3) F)ˣ).symm = involutionHomeomorph :=
  rfl

private theorem involutionHomeomorph_preimage (S : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :
    (involutionHomeomorph : (Matrix (Fin 3) (Fin 3) F)ˣ ≃ₜ (Matrix (Fin 3) (Fin 3) F)ˣ) ⁻¹' S =
      involutionUnit ⁻¹' S := rfl

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

namespace BruhatCellsGL3

variable {F : Type*} [Field F]

section Unipotent

variable (x y z x' y' z' : F)

private theorem unitriangular_mul :
    unitriangular x y z * unitriangular x' y' z' = unitriangular (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriangular, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem unitriangular_mul_unitriangular_neg :
    unitriangular x y z * unitriangular (-x) (-y) (x * y - z) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriangular, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem unitriangular_neg_mul_unitriangular :
    unitriangular (-x) (-y) (x * y - z) * unitriangular x y z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitriangular, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def unitriangularUnit : (Matrix (Fin 3) (Fin 3) F)ˣ where
  val := unitriangular x y z
  inv := unitriangular (-x) (-y) (x * y - z)
  val_inv := unitriangular_mul_unitriangular_neg x y z
  inv_val := unitriangular_neg_mul_unitriangular x y z

@[scoped simp] private theorem unitriangularUnit_val :
    ((unitriangularUnit x y z : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) = unitriangular x y z :=
  rfl

@[scoped simp] private theorem unitriangularUnit_inv_val :
    (((unitriangularUnit x y z)⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      unitriangular (-x) (-y) (x * y - z) := rfl

end Unipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Stability

variable {x y z : F}

private theorem mem_preimage_iff_unitriangularUnit_mul {C : Set (Matrix (Fin 3) (Fin 3) F)}
    (hC : ∀ x y z : F, ∀ g ∈ C, unitriangular x y z * g ∈ C) (u : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    u ∈ Units.val ⁻¹' C ↔ unitriangularUnit x y z * u ∈ Units.val ⁻¹' C := by
  refine ⟨fun h => mul_mem_preimage_of_val_eq (hC x y z) (unitriangularUnit_val x y z) h, fun h => ?_⟩
  have h' := mul_mem_preimage_of_val_eq (hC (-x) (-y) (x * y - z)) (unitriangularUnit_inv_val x y z) h
  rwa [inv_mul_cancel_left] at h'

private theorem mem_preimage_iff_mul_unitriangularUnit {C : Set (Matrix (Fin 3) (Fin 3) F)}
    (hC : ∀ x y z : F, ∀ g ∈ C, g * unitriangular x y z ∈ C) (u : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    u ∈ Units.val ⁻¹' C ↔ u * unitriangularUnit x y z ∈ Units.val ⁻¹' C := by
  refine ⟨fun h => mul_mem_preimage_of_val_eq' (hC x y z) (unitriangularUnit_val x y z) h, fun h => ?_⟩
  have h' := mul_mem_preimage_of_val_eq' (hC (-x) (-y) (x * y - z)) (unitriangularUnit_inv_val x y z) h
  rwa [mul_inv_cancel_right] at h'

variable (u : (Matrix (Fin 3) (Fin 3) F)ˣ)

private theorem mem_bigCellGL_iff_unitriangularUnit_mul : u ∈ bigCellGL ↔ unitriangularUnit x y z * u ∈ bigCellGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_bigCell h) u

private theorem mem_bigCellGL_iff_mul_unitriangularUnit : u ∈ bigCellGL ↔ u * unitriangularUnit x y z ∈ bigCellGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_bigCell h) u

private theorem mem_cycleCell123GL_iff_unitriangularUnit_mul :
    u ∈ cycleCell123GL ↔ unitriangularUnit x y z * u ∈ cycleCell123GL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_cycleCell123 h) u

private theorem mem_cycleCell123GL_iff_mul_unitriangularUnit :
    u ∈ cycleCell123GL ↔ u * unitriangularUnit x y z ∈ cycleCell123GL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_cycleCell123 h) u

private theorem mem_cycleCell132GL_iff_unitriangularUnit_mul :
    u ∈ cycleCell132GL ↔ unitriangularUnit x y z * u ∈ cycleCell132GL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_cycleCell132 h) u

private theorem mem_cycleCell132GL_iff_mul_unitriangularUnit :
    u ∈ cycleCell132GL ↔ u * unitriangularUnit x y z ∈ cycleCell132GL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_cycleCell132 h) u

private
theorem mem_reflCell12GL_iff_unitriangularUnit_mul : u ∈ reflCell12GL ↔ unitriangularUnit x y z * u ∈ reflCell12GL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_reflCell12 h) u

private
theorem mem_reflCell12GL_iff_mul_unitriangularUnit : u ∈ reflCell12GL ↔ u * unitriangularUnit x y z ∈ reflCell12GL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_reflCell12 h) u

private
theorem mem_reflCell23GL_iff_unitriangularUnit_mul : u ∈ reflCell23GL ↔ unitriangularUnit x y z * u ∈ reflCell23GL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_reflCell23 h) u

private
theorem mem_reflCell23GL_iff_mul_unitriangularUnit : u ∈ reflCell23GL ↔ u * unitriangularUnit x y z ∈ reflCell23GL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_reflCell23 h) u

private
theorem mem_borelCellGL_iff_unitriangularUnit_mul : u ∈ borelCellGL ↔ unitriangularUnit x y z * u ∈ borelCellGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_borelCell h) u

private
theorem mem_borelCellGL_iff_mul_unitriangularUnit : u ∈ borelCellGL ↔ u * unitriangularUnit x y z ∈ borelCellGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_borelCell h) u

private
theorem mem_cycleCellsGL_iff_unitriangularUnit_mul : u ∈ cycleCellsGL ↔ unitriangularUnit x y z * u ∈ cycleCellsGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_cycleCells h) u

private
theorem mem_cycleCellsGL_iff_mul_unitriangularUnit : u ∈ cycleCellsGL ↔ u * unitriangularUnit x y z ∈ cycleCellsGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_cycleCells h) u

private
theorem mem_reflCellsGL_iff_unitriangularUnit_mul : u ∈ reflCellsGL ↔ unitriangularUnit x y z * u ∈ reflCellsGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_reflCells h) u

private
theorem mem_reflCellsGL_iff_mul_unitriangularUnit : u ∈ reflCellsGL ↔ u * unitriangularUnit x y z ∈ reflCellsGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_reflCells h) u

private theorem mem_stageOneGL_iff_unitriangularUnit_mul : u ∈ stageOneGL ↔ unitriangularUnit x y z * u ∈ stageOneGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_stageOne h) u

private theorem mem_stageOneGL_iff_mul_unitriangularUnit : u ∈ stageOneGL ↔ u * unitriangularUnit x y z ∈ stageOneGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_stageOne h) u

private theorem mem_stageTwoGL_iff_unitriangularUnit_mul : u ∈ stageTwoGL ↔ unitriangularUnit x y z * u ∈ stageTwoGL :=
  mem_preimage_iff_unitriangularUnit_mul (fun _ _ _ _ h => unitriangular_mul_mem_stageTwo h) u

private theorem mem_stageTwoGL_iff_mul_unitriangularUnit : u ∈ stageTwoGL ↔ u * unitriangularUnit x y z ∈ stageTwoGL :=
  mem_preimage_iff_mul_unitriangularUnit (fun _ _ _ _ h => mul_unitriangular_mem_stageTwo h) u

private theorem mem_bigCellGL_union_cycleCell123GL_iff_unitriangularUnit_mul :
    u ∈ bigCellGL ∪ cycleCell123GL ↔ unitriangularUnit x y z * u ∈ bigCellGL ∪ cycleCell123GL :=
  mem_union_iff_of_mem_iff mem_bigCellGL_iff_unitriangularUnit_mul mem_cycleCell123GL_iff_unitriangularUnit_mul u

private theorem mem_bigCellGL_union_cycleCell123GL_iff_mul_unitriangularUnit :
    u ∈ bigCellGL ∪ cycleCell123GL ↔ u * unitriangularUnit x y z ∈ bigCellGL ∪ cycleCell123GL :=
  mem_union_iff_of_mem_iff mem_bigCellGL_iff_mul_unitriangularUnit mem_cycleCell123GL_iff_mul_unitriangularUnit u

private theorem mem_stageOneGL_union_reflCell12GL_iff_unitriangularUnit_mul :
    u ∈ stageOneGL ∪ reflCell12GL ↔ unitriangularUnit x y z * u ∈ stageOneGL ∪ reflCell12GL :=
  mem_union_iff_of_mem_iff mem_stageOneGL_iff_unitriangularUnit_mul mem_reflCell12GL_iff_unitriangularUnit_mul u

private theorem mem_stageOneGL_union_reflCell12GL_iff_mul_unitriangularUnit :
    u ∈ stageOneGL ∪ reflCell12GL ↔ u * unitriangularUnit x y z ∈ stageOneGL ∪ reflCell12GL :=
  mem_union_iff_of_mem_iff mem_stageOneGL_iff_mul_unitriangularUnit mem_reflCell12GL_iff_mul_unitriangularUnit u

end Stability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Pieces

private theorem union_diff_left_eq {α : Type*} {s t : Set α} (h : ∀ a ∈ t, a ∉ s) : (s ∪ t) \ s = t := by
  ext a
  constructor
  · rintro ⟨ha | ha, hn⟩
    · exact absurd ha hn
    · exact ha
  · intro ha
    exact ⟨Or.inr ha, h a ha⟩

private theorem stageOneGL_eq_union_cycleCell132GL :
    (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = bigCellGL ∪ cycleCell123GL ∪ cycleCell132GL := by
  rw [stageOneGL_eq, cycleCellsGL_eq, Set.union_assoc]

private theorem stageTwoGL_eq_union_reflCell23GL :
    (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageOneGL ∪ reflCell12GL ∪ reflCell23GL := by
  rw [stageTwoGL_eq, reflCellsGL_eq, Set.union_assoc]

private theorem notMem_stageOneGL_of_mem_reflCellsGL {u : (Matrix (Fin 3) (Fin 3) F)ˣ} (h : u ∈ reflCellsGL) :
    u ∉ stageOneGL := by
  rw [reflCellsGL_eq_diff] at h
  exact h.2

private theorem bigCellGL_eq_diff_empty : (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = bigCellGL \ ∅ := by
  ext u
  exact ⟨fun h => ⟨h, fun h' => h'⟩, fun h => h.1⟩

private theorem cycleCell123GL_eq_diff_bigCellGL :
    (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = (bigCellGL ∪ cycleCell123GL) \ bigCellGL := by
  refine (union_diff_left_eq fun u hu hb => ?_).symm
  exact ((mem_bigCell_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hb).1
    ((mem_cycleCell123_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hu).1

private theorem cycleCell132GL_eq_diff_union :
    (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageOneGL \ (bigCellGL ∪ cycleCell123GL) := by
  rw [stageOneGL_eq_union_cycleCell132GL]
  refine (union_diff_left_eq fun u hu h => ?_).symm
  have hu' := (mem_cycleCell132_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hu
  rcases h with hb | hc
  · exact ((mem_bigCell_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hb).2 hu'.2
  · exact hu'.1 ((mem_cycleCell123_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hc).1

private theorem reflCell12GL_eq_diff_stageOneGL :
    (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = (stageOneGL ∪ reflCell12GL) \ stageOneGL :=
  (union_diff_left_eq fun _ hu => notMem_stageOneGL_of_mem_reflCellsGL (reflCell12GL_subset hu)).symm

private theorem reflCell23GL_eq_diff_union :
    (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = stageTwoGL \ (stageOneGL ∪ reflCell12GL) := by
  rw [stageTwoGL_eq_union_reflCell23GL]
  refine (union_diff_left_eq fun u hu h => ?_).symm
  rcases h with hs | h12
  · exact notMem_stageOneGL_of_mem_reflCellsGL (reflCell23GL_subset hu) hs
  · exact ((mem_reflCell12_iff (u : Matrix (Fin 3) (Fin 3) F)).mp h12).2.2
      ((mem_reflCell23_iff (u : Matrix (Fin 3) (Fin 3) F)).mp hu).2.1

private
theorem borelCellGL_eq_univ_diff : (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) = Set.univ \ stageTwoGL := by
  rw [borelCellGL_eq_compl]
  ext u
  exact ⟨fun h => ⟨Set.mem_univ u, h⟩, fun h => h.2⟩

private theorem bigCellGL_subset_self : (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ bigCellGL := fun _ h => h

private theorem cycleCell123GL_subset_union :
    (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ bigCellGL ∪ cycleCell123GL :=
  fun _ h => Or.inr h

private theorem cycleCell132GL_subset_stageOneGL : (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageOneGL :=
  fun _ h => cycleCellsGL_subset (cycleCell132GL_subset h)

private theorem reflCell12GL_subset_union :
    (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageOneGL ∪ reflCell12GL :=
  fun _ h => Or.inr h

private theorem reflCell23GL_subset_stageTwoGL : (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageTwoGL :=
  fun _ h => reflCellsGL_subset (reflCell23GL_subset h)

private theorem bigCellGL_union_cycleCell123GL_subset_stageOneGL :
    (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageOneGL := by
  rw [stageOneGL_eq_union_cycleCell132GL]
  exact Set.subset_union_left

private theorem stageOneGL_union_reflCell12GL_subset_stageTwoGL :
    (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ⊆ stageTwoGL := by
  rw [stageTwoGL_eq_union_reflCell23GL]
  exact Set.subset_union_left

private theorem bigCellGL_union_cycleCell123GL_eq_inter :
    (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      stageOneGL ∩ (bigCellGL ∪ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | lowerLeftMinor2 g ≠ 0}) := by
  ext u
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, mem_bigCellGL, mem_cycleCell123GL,
    mem_stageOneGL, stageOne, cycleCells, mem_bigCell_iff, mem_cycleCell123_iff, mem_cycleCell132_iff, ne_eq]
  tauto

private theorem stageOneGL_union_reflCell12GL_eq_inter :
    (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) =
      stageTwoGL ∩ (stageOneGL ∪ Units.val ⁻¹' {g : Matrix (Fin 3) (Fin 3) F | g 1 0 ≠ 0}) := by
  ext u
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, mem_stageOneGL, mem_reflCell12GL,
    mem_stageTwoGL, stageTwo, stageOne, cycleCells, reflCells, mem_bigCell_iff, mem_cycleCell123_iff,
    mem_cycleCell132_iff, mem_reflCell12_iff, mem_reflCell23_iff, ne_eq]
  tauto

end Pieces
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Topology

variable [TopologicalSpace F]

private theorem isClosed_val_preimage_of_eq_diff {X : Type*} [TopologicalSpace X] {U V C : Set X} (hV : IsOpen V)
    (hC : C = U \ V) : IsClosed (Subtype.val ⁻¹' C : Set U) := by
  subst hC
  have h : (Subtype.val ⁻¹' (U \ V) : Set U) = Subtype.val ⁻¹' Vᶜ := by
    ext u
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  rw [h]
  exact (isClosed_compl_iff.mpr hV).preimage continuous_subtype_val

private theorem isClosed_piece_bigCellGL :
    IsClosed (Subtype.val ⁻¹' bigCellGL : Set (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_empty bigCellGL_eq_diff_empty

variable [T1Space F] [IsTopologicalRing F]

private theorem isOpen_bigCellGL_union_cycleCell123GL :
    IsOpen (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) := by
  rw [bigCellGL_union_cycleCell123GL_eq_inter]
  exact isOpen_stageOneGL.inter (isOpen_bigCellGL.union isOpen_preimage_lowerLeftMinor2_ne_zero)

private theorem isOpen_stageOneGL_union_reflCell12GL :
    IsOpen (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) := by
  rw [stageOneGL_union_reflCell12GL_eq_inter]
  exact isOpen_stageTwoGL.inter (isOpen_stageOneGL.union isOpen_preimage_entry_one_zero_ne_zero)

private theorem isClosed_piece_cycleCell123GL :
    IsClosed (Subtype.val ⁻¹' cycleCell123GL : Set (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_bigCellGL cycleCell123GL_eq_diff_bigCellGL

private theorem isClosed_piece_cycleCell132GL :
    IsClosed (Subtype.val ⁻¹' cycleCell132GL : Set (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_bigCellGL_union_cycleCell123GL cycleCell132GL_eq_diff_union

private theorem isClosed_piece_reflCell12GL :
    IsClosed (Subtype.val ⁻¹' reflCell12GL : Set (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_stageOneGL reflCell12GL_eq_diff_stageOneGL

private theorem isClosed_piece_reflCell23GL :
    IsClosed (Subtype.val ⁻¹' reflCell23GL : Set (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_stageOneGL_union_reflCell12GL reflCell23GL_eq_diff_union

private theorem isClosed_piece_borelCellGL :
    IsClosed (Subtype.val ⁻¹' borelCellGL : Set (Set.univ : Set (Matrix (Fin 3) (Fin 3) F)ˣ)) :=
  isClosed_val_preimage_of_eq_diff isOpen_stageTwoGL borelCellGL_eq_univ_diff

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatSpace SchwartzBruhatIntegral SchwartzBruhatIntegral.BallData BruhatCellsGL3
open LanglandsTunnell.TateLocal WhittakerCoinvariantsGL3.Descent

namespace WhittakerCoinvariantsGL3

section Model

variable {Y M : Type*} [TopologicalSpace Y] [TopologicalSpace M]

private theorem eq_zero_of_model (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) {ι : Type*}
    (R : ι → Y ≃ₜ Y) (S : ι → M ≃ₜ M) (hS : ∀ i y, e (R i y) = S i (e y)) (c : ι → ℂ)
    (hE : ∀ i, ∀ h : testSpace Y, E (c i • comapHomeomorph (R i) h) = E h)
    (ΘY : Y ≃ₜ Y) (ΘM : M ≃ₜ M) (hΘ : ∀ y, e (ΘY y) = ΘM (e y))
    (hanti : ∀ h : testSpace Y, E (comapHomeomorph ΘY h) = -E h)
    (hcell : ∀ T : (M → ℂ) →ₗ[ℂ] ℂ,
      (∀ i, ∀ f : M → ℂ, IsSchwartzBruhat f → T (fun x => c i * f (S i x)) = T f) →
        ∀ f : M → ℂ, IsSchwartzBruhat f → T (f ∘ ΘM) = T f) :
    E = 0 := by
  obtain ⟨T, hT⟩ := exists_extension (transport E e)
  have hlaw : ∀ i, ∀ f : M → ℂ, IsSchwartzBruhat f → T (fun x => c i * f (S i x)) = T f := by
    intro i f hf
    have h₁ := transport_smul_comapHomeomorph E e (R i) (S i) (hS i) (c i) 1
      (fun h => by rw [hE i h, one_smul]) ⟨f, hf⟩
    rw [one_smul, ← hT, ← hT] at h₁
    exact h₁
  have hsymm : ∀ h : testSpace Y, E (comapHomeomorph ΘY h) = E h := by
    intro h
    have h₁ := smul_comapHomeomorph_of_transport E e ΘY ΘM hΘ 1 1 (fun f => by
      rw [one_smul, one_smul, ← hT, ← hT]
      exact hcell T hlaw f f.2) h
    rw [one_smul, one_smul] at h₁
    exact h₁
  exact eq_zero_of_forall_eq_neg hsymm hanti

private theorem eq_zero_of_model' (E : testSpace Y →ₗ[ℂ] ℂ) (e : Y ≃ₜ M) {ι : Type*}
    (R : ι → Y ≃ₜ Y) (S : ι → M ≃ₜ M) (hS : ∀ i y, e (R i y) = S i (e y)) (c : ι → ℂ)
    (hE : ∀ i, ∀ h : testSpace Y, E (c i • comapHomeomorph (R i) h) = E h)
    (hcell : ∀ T : (M → ℂ) →ₗ[ℂ] ℂ,
      (∀ i, ∀ f : M → ℂ, IsSchwartzBruhat f → T (fun x => c i * f (S i x)) = T f) →
        ∀ f : M → ℂ, IsSchwartzBruhat f → T f = 0) :
    E = 0 := by
  obtain ⟨T, hT⟩ := exists_extension (transport E e)
  have hlaw : ∀ i, ∀ f : M → ℂ, IsSchwartzBruhat f → T (fun x => c i * f (S i x)) = T f := by
    intro i f hf
    have h₁ := transport_smul_comapHomeomorph E e (R i) (S i) (hS i) (c i) 1
      (fun h => by rw [hE i h, one_smul]) ⟨f, hf⟩
    rw [one_smul, ← hT, ← hT] at h₁
    exact h₁
  refine LinearMap.ext fun h => ?_
  have h₁ : transport E e ((comapHomeomorph e).symm h) = 0 := by
    rw [← hT]
    exact hcell T hlaw _ ((comapHomeomorph e).symm h).2
  rw [transport_apply, LinearEquiv.apply_symm_apply] at h₁
  rw [LinearMap.zero_apply]
  exact h₁

end Model
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Laws

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def lawHomeo : RootIndex × F → (Matrix (Fin 3) (Fin 3) F)ˣ ≃ₜ (Matrix (Fin 3) (Fin 3) F)ˣ
  | (.left12, s) => Homeomorph.mulLeft (unitriangularUnit s 0 0)
  | (.left23, s) => Homeomorph.mulLeft (unitriangularUnit 0 s 0)
  | (.left13, s) => Homeomorph.mulLeft (unitriangularUnit 0 0 s)
  | (.right12, s) => Homeomorph.mulRight (unitriangularUnit s 0 0)
  | (.right23, s) => Homeomorph.mulRight (unitriangularUnit 0 s 0)
  | (.right13, s) => Homeomorph.mulRight (unitriangularUnit 0 0 s)

private theorem val_lawHomeo_left12 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.left12, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      rootGen12 s * g :=
  congrArg (· * (g : Matrix (Fin 3) (Fin 3) F)) (unitriangularUnit_val s 0 0)

private theorem val_lawHomeo_left23 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.left23, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      rootGen23 s * g :=
  congrArg (· * (g : Matrix (Fin 3) (Fin 3) F)) (unitriangularUnit_val 0 s 0)

private theorem val_lawHomeo_left13 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.left13, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      rootGen13 s * g :=
  congrArg (· * (g : Matrix (Fin 3) (Fin 3) F)) (unitriangularUnit_val 0 0 s)

private theorem val_lawHomeo_right12 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.right12, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      g * rootGen12 s :=
  congrArg ((g : Matrix (Fin 3) (Fin 3) F) * ·) (unitriangularUnit_val s 0 0)

private theorem val_lawHomeo_right23 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.right23, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      g * rootGen23 s :=
  congrArg ((g : Matrix (Fin 3) (Fin 3) F) * ·) (unitriangularUnit_val 0 s 0)

private theorem val_lawHomeo_right13 (s : F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    ((lawHomeo (RootIndex.right13, s) g : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) =
      g * rootGen13 s :=
  congrArg ((g : Matrix (Fin 3) (Fin 3) F) * ·) (unitriangularUnit_val 0 0 s)

end Laws
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Cells

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

section BigCell

variable [ContinuousInv₀ F]

private theorem bigCell_conj (hC : ∀ i g, g ∈ bigCellGL ↔
      lawHomeo i g ∈ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL}) :
    bigCellHomeomorph ((lawHomeo i).subtype (hC i) y) =
      bigCellHomeo i (bigCellHomeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = bigCellHomeomorph.symm x :=
    ⟨bigCellHomeomorph y, (bigCellHomeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (bigCellHomeomorph.symm x) =
      bigCellHomeomorph.symm (bigCellHomeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_bigCellRight12 s x).symm
  · exact (val_lawHomeo_right23 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_bigCellRight23 s x).symm
  · exact (val_lawHomeo_right13 s (bigCellHomeomorph.symm x).1).trans
      (bigCellPoint_bigCellRight13 s x).symm

private theorem bigCell_conjInv
    (hΘ : ∀ g, g ∈ bigCellGL ↔
      involutionHomeomorph g ∈ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL}) :
    bigCellHomeomorph (involutionHomeomorph.subtype hΘ y) =
      bigCellInvolutionHomeomorph (bigCellHomeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = bigCellHomeomorph.symm x :=
    ⟨bigCellHomeomorph y, (bigCellHomeomorph.symm_apply_apply y).symm⟩
  suffices h : involutionHomeomorph.subtype hΘ (bigCellHomeomorph.symm x) =
      bigCellHomeomorph.symm (bigCellInvolutionHomeomorph x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  exact (val_involutionHomeomorph_apply (bigCellHomeomorph.symm x).1).trans
    (bigCellPoint_bigCellInvolution x).symm

private theorem bigCell_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F × F)))
    (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F × F))))
    (hP : D.IsAdmissibleAut bigPerm)
    (hC : ∀ i g, g ∈ bigCellGL ↔
      lawHomeo i g ∈ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (hΘ : ∀ g, g ∈ bigCellGL ↔
      involutionHomeomorph g ∈ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h)
    (hanti : ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL},
      E (comapHomeomorph (involutionHomeomorph.subtype hΘ) h) = -E h) :
    E = 0 :=
  eq_zero_of_model E bigCellHomeomorph (fun i => (lawHomeo i).subtype (hC i)) bigCellHomeo
    (bigCell_conj hC) (rootCoeff χ) hE (involutionHomeomorph.subtype hΘ)
    bigCellInvolutionHomeomorph (bigCell_conjInv hΘ) hanti
    (fun T hT _ hf => bigCell_apply_comp_involution_eq hF hY hYc χ hχ D hc hP T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (bigCellHomeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

end BigCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell123

variable [ContinuousInv₀ F]

private theorem cycleCell123_conj (hC : ∀ i g, g ∈ cycleCell123GL ↔
      lawHomeo i g ∈ (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL}) :
    cycleCell123Homeomorph ((lawHomeo i).subtype (hC i) y) =
      cycle123Homeo i (cycleCell123Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = cycleCell123Homeomorph.symm x :=
    ⟨cycleCell123Homeomorph y, (cycleCell123Homeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (cycleCell123Homeomorph.symm x) =
      cycleCell123Homeomorph.symm (cycle123Homeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_cycle123Right12 s x).symm
  · exact (val_lawHomeo_right23 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_cycle123Right23 s x).symm
  · exact (val_lawHomeo_right13 s (cycleCell123Homeomorph.symm x).1).trans
      (cycleCell123Point_cycle123Right13 s x).symm

private theorem cycleCell123_conjInv
    (hΘ : ∀ g, g ∈ cycleCell123GL ↔
      involutionHomeomorph g ∈ (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL}) :
    cycleCell123Homeomorph (involutionHomeomorph.subtype hΘ y) =
      cycle123InvolutionHomeomorph (cycleCell123Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = cycleCell123Homeomorph.symm x :=
    ⟨cycleCell123Homeomorph y, (cycleCell123Homeomorph.symm_apply_apply y).symm⟩
  suffices h : involutionHomeomorph.subtype hΘ (cycleCell123Homeomorph.symm x) =
      cycleCell123Homeomorph.symm (cycle123InvolutionHomeomorph x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  exact (val_involutionHomeomorph_apply (cycleCell123Homeomorph.symm x).1).trans
    (cycleCell123Point_cycle123Involution x).symm

private theorem cycleCell123_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F))) (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F))))
    (hP : D.IsAdmissibleAut perm123)
    (hC : ∀ i g, g ∈ cycleCell123GL ↔
      lawHomeo i g ∈ (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (hΘ : ∀ g, g ∈ cycleCell123GL ↔
      involutionHomeomorph g ∈ (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h)
    (hanti : ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL},
      E (comapHomeomorph (involutionHomeomorph.subtype hΘ) h) = -E h) :
    E = 0 :=
  eq_zero_of_model E cycleCell123Homeomorph (fun i => (lawHomeo i).subtype (hC i)) cycle123Homeo
    (cycleCell123_conj hC) (rootCoeff χ) hE (involutionHomeomorph.subtype hΘ)
    cycle123InvolutionHomeomorph (cycleCell123_conjInv hΘ) hanti
    (fun T hT _ hf => cycle123_apply_comp_involution_eq hF hY hYc χ hχ1 hχ D hc hP T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (cycle123Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

end CycleCell123
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section CycleCell132

variable [ContinuousInv₀ F]

private theorem cycleCell132_conj (hC : ∀ i g, g ∈ cycleCell132GL ↔
      lawHomeo i g ∈ (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL}) :
    cycleCell132Homeomorph ((lawHomeo i).subtype (hC i) y) =
      cycle132Homeo i (cycleCell132Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = cycleCell132Homeomorph.symm x :=
    ⟨cycleCell132Homeomorph y, (cycleCell132Homeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (cycleCell132Homeomorph.symm x) =
      cycleCell132Homeomorph.symm (cycle132Homeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_cycle132Right12 s x).symm
  · exact (val_lawHomeo_right23 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_cycle132Right23 s x).symm
  · exact (val_lawHomeo_right13 s (cycleCell132Homeomorph.symm x).1).trans
      (cycleCell132Point_cycle132Right13 s x).symm

private theorem cycleCell132_conjInv
    (hΘ : ∀ g, g ∈ cycleCell132GL ↔
      involutionHomeomorph g ∈ (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL}) :
    cycleCell132Homeomorph (involutionHomeomorph.subtype hΘ y) =
      cycle132InvolutionHomeomorph (cycleCell132Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = cycleCell132Homeomorph.symm x :=
    ⟨cycleCell132Homeomorph y, (cycleCell132Homeomorph.symm_apply_apply y).symm⟩
  suffices h : involutionHomeomorph.subtype hΘ (cycleCell132Homeomorph.symm x) =
      cycleCell132Homeomorph.symm (cycle132InvolutionHomeomorph x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  exact (val_involutionHomeomorph_apply (cycleCell132Homeomorph.symm x).1).trans
    (cycleCell132Point_cycle132Involution x).symm

private theorem cycleCell132_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F))) (hc : IsCompact (D.ref : Set ((F × F × F) × (F × F))))
    (hP : D.IsAdmissibleAut perm132)
    (hC : ∀ i g, g ∈ cycleCell132GL ↔
      lawHomeo i g ∈ (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (hΘ : ∀ g, g ∈ cycleCell132GL ↔
      involutionHomeomorph g ∈ (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h)
    (hanti : ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL},
      E (comapHomeomorph (involutionHomeomorph.subtype hΘ) h) = -E h) :
    E = 0 :=
  eq_zero_of_model E cycleCell132Homeomorph (fun i => (lawHomeo i).subtype (hC i)) cycle132Homeo
    (cycleCell132_conj hC) (rootCoeff χ) hE (involutionHomeomorph.subtype hΘ)
    cycle132InvolutionHomeomorph (cycleCell132_conjInv hΘ) hanti
    (fun T hT _ hf => cycle132_apply_comp_involution_eq hF hY hYc χ hχ1 hχ D hc hP T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (cycle132Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

end CycleCell132
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell12

variable [ContinuousInv₀ F]

private theorem reflCell12_conj (hC : ∀ i g, g ∈ reflCell12GL ↔
      lawHomeo i g ∈ (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL}) :
    reflCell12Homeomorph ((lawHomeo i).subtype (hC i) y) =
      refl12Homeo i (reflCell12Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = reflCell12Homeomorph.symm x :=
    ⟨reflCell12Homeomorph y, (reflCell12Homeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (reflCell12Homeomorph.symm x) =
      reflCell12Homeomorph.symm (refl12Homeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_refl12Right12 s x).symm
  · exact (val_lawHomeo_right23 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_refl12Right23 s x).symm
  · exact (val_lawHomeo_right13 s (reflCell12Homeomorph.symm x).1).trans
      (reflCell12Point_refl12Right13 s x).symm

private theorem reflCell12_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1)
    (hC : ∀ i g, g ∈ reflCell12GL ↔
      lawHomeo i g ∈ (reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell12GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E reflCell12Homeomorph (fun i => (lawHomeo i).subtype (hC i)) refl12Homeo
    (reflCell12_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => refl12_apply_eq_zero hF hY hYc χ hχ1 T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (refl12Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

end ReflCell12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section ReflCell23

variable [ContinuousInv₀ F]

private theorem reflCell23_conj (hC : ∀ i g, g ∈ reflCell23GL ↔
      lawHomeo i g ∈ (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL}) :
    reflCell23Homeomorph ((lawHomeo i).subtype (hC i) y) =
      refl23Homeo i (reflCell23Homeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = reflCell23Homeomorph.symm x :=
    ⟨reflCell23Homeomorph y, (reflCell23Homeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (reflCell23Homeomorph.symm x) =
      reflCell23Homeomorph.symm (refl23Homeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_refl23Right12 s x).symm
  · exact (val_lawHomeo_right23 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_refl23Right23 s x).symm
  · exact (val_lawHomeo_right13 s (reflCell23Homeomorph.symm x).1).trans
      (reflCell23Point_refl23Right13 s x).symm

private theorem reflCell23_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1)
    (hC : ∀ i g, g ∈ reflCell23GL ↔
      lawHomeo i g ∈ (reflCell23GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ reflCell23GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E reflCell23Homeomorph (fun i => (lawHomeo i).subtype (hC i)) refl23Homeo
    (reflCell23_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => refl23_apply_eq_zero hF hY hYc χ hχ1 T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (refl23Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

end ReflCell23
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section BorelCell

variable [ContinuousInv₀ F]

private theorem borelCell_conj (hC : ∀ i g, g ∈ borelCellGL ↔
      lawHomeo i g ∈ (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (i : RootIndex × F) (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL}) :
    borelCellHomeomorph ((lawHomeo i).subtype (hC i) y) =
      borelHomeo i (borelCellHomeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = borelCellHomeomorph.symm x :=
    ⟨borelCellHomeomorph y, (borelCellHomeomorph.symm_apply_apply y).symm⟩
  suffices h : (lawHomeo i).subtype (hC i) (borelCellHomeomorph.symm x) =
      borelCellHomeomorph.symm (borelHomeo i x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · exact (val_lawHomeo_left12 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_leftRoot12 s x).symm
  · exact (val_lawHomeo_left23 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_leftRoot23 s x).symm
  · exact (val_lawHomeo_left13 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_leftRoot13 s x).symm
  · exact (val_lawHomeo_right12 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_borelRight12 s x).symm
  · exact (val_lawHomeo_right23 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_borelRight23 s x).symm
  · exact (val_lawHomeo_right13 s (borelCellHomeomorph.symm x).1).trans
      (borelCellPoint_borelRight13 s x).symm

private theorem borelCell_conjInv
    (hΘ : ∀ g, g ∈ borelCellGL ↔
      involutionHomeomorph g ∈ (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (y : {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL}) :
    borelCellHomeomorph (involutionHomeomorph.subtype hΘ y) =
      borelInvolutionHomeomorph (borelCellHomeomorph y) := by
  obtain ⟨x, rfl⟩ : ∃ x, y = borelCellHomeomorph.symm x :=
    ⟨borelCellHomeomorph y, (borelCellHomeomorph.symm_apply_apply y).symm⟩
  suffices h : involutionHomeomorph.subtype hΘ (borelCellHomeomorph.symm x) =
      borelCellHomeomorph.symm (borelInvolutionHomeomorph x) by
    rw [h, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  exact (val_involutionHomeomorph_apply (borelCellHomeomorph.symm x).1).trans
    (borelCellPoint_borelInvolution x).symm

private theorem borelCell_kill [T2Space F] (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D : BallData (F × F × F)) (hc : IsCompact (D.ref : Set (F × F × F)))
    (hP : D.IsAdmissibleAut swapAB)
    (hC : ∀ i g, g ∈ borelCellGL ↔
      lawHomeo i g ∈ (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (hΘ : ∀ g, g ∈ borelCellGL ↔
      involutionHomeomorph g ∈ (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h)
    (hanti : ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL},
      E (comapHomeomorph (involutionHomeomorph.subtype hΘ) h) = -E h) :
    E = 0 :=
  eq_zero_of_model E borelCellHomeomorph (fun i => (lawHomeo i).subtype (hC i)) borelHomeo
    (borelCell_conj hC) (rootCoeff χ) hE (involutionHomeomorph.subtype hΘ)
    borelInvolutionHomeomorph (borelCell_conjInv hΘ) hanti
    (fun T hT _ hf => borel_apply_comp_involution_eq hF hY hYc χ hχ1 hχ D hc hP T
      (fun i g hg => (congrArg T (toLin_opOfMapLast (rootCoeff χ i) (borelHomeo_torus i) g)).trans
        (hT i g (mem_sbSubmodule.mp hg))) hf)

end BorelCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end Cells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Chain

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

private theorem Descent.VanishesOn.of_eq_diff {Λ : testSpace X →ₗ[ℂ] ℂ} {U V C : Set X}
    (h : Descent.VanishesOn Λ V) (hC : C = U \ V) : Descent.VanishesOn Λ (U \ C) := by
  refine h.mono fun x hx => ?_
  subst hC
  by_contra hxV
  exact hx.2 ⟨hx.1, hxV⟩

end Chain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Group

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private theorem mem_iff_lawHomeo_mem {S : Set (Matrix (Fin 3) (Fin 3) F)ˣ}
    (hl : ∀ x y z : F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ, g ∈ S ↔ unitriangularUnit x y z * g ∈ S)
    (hr : ∀ x y z : F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ, g ∈ S ↔ g * unitriangularUnit x y z ∈ S) :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ, g ∈ S ↔ lawHomeo i g ∈ S := by
  rintro ⟨_ | _ | _ | _ | _ | _, s⟩ g
  · exact hl s 0 0 g
  · exact hl 0 s 0 g
  · exact hl 0 0 s g
  · exact hr s 0 0 g
  · exact hr 0 s 0 g
  · exact hr 0 0 s g

private theorem mem_bigCellGL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ bigCellGL ↔ lawHomeo i g ∈ bigCellGL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_bigCellGL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_bigCellGL_iff_mul_unitriangularUnit g)

private theorem mem_cycleCell123GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ cycleCell123GL ↔ lawHomeo i g ∈ cycleCell123GL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_cycleCell123GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_cycleCell123GL_iff_mul_unitriangularUnit g)

private theorem mem_cycleCell132GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ cycleCell132GL ↔ lawHomeo i g ∈ cycleCell132GL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_cycleCell132GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_cycleCell132GL_iff_mul_unitriangularUnit g)

private theorem mem_reflCell12GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ reflCell12GL ↔ lawHomeo i g ∈ reflCell12GL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_reflCell12GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_reflCell12GL_iff_mul_unitriangularUnit g)

private theorem mem_reflCell23GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ reflCell23GL ↔ lawHomeo i g ∈ reflCell23GL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_reflCell23GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_reflCell23GL_iff_mul_unitriangularUnit g)

private theorem mem_borelCellGL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ borelCellGL ↔ lawHomeo i g ∈ borelCellGL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_borelCellGL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_borelCellGL_iff_mul_unitriangularUnit g)

private theorem mem_stageOneGL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ stageOneGL ↔ lawHomeo i g ∈ stageOneGL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_stageOneGL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_stageOneGL_iff_mul_unitriangularUnit g)

private theorem mem_stageTwoGL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ stageTwoGL ↔ lawHomeo i g ∈ stageTwoGL :=
  mem_iff_lawHomeo_mem (fun _ _ _ g => mem_stageTwoGL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_stageTwoGL_iff_mul_unitriangularUnit g)

private theorem mem_bigCellGL_union_cycleCell123GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ bigCellGL ∪ cycleCell123GL ↔ lawHomeo i g ∈ bigCellGL ∪ cycleCell123GL :=
  mem_iff_lawHomeo_mem
    (fun _ _ _ g => mem_bigCellGL_union_cycleCell123GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_bigCellGL_union_cycleCell123GL_iff_mul_unitriangularUnit g)

private theorem mem_stageOneGL_union_reflCell12GL_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ stageOneGL ∪ reflCell12GL ↔ lawHomeo i g ∈ stageOneGL ∪ reflCell12GL :=
  mem_iff_lawHomeo_mem
    (fun _ _ _ g => mem_stageOneGL_union_reflCell12GL_iff_unitriangularUnit_mul g)
    (fun _ _ _ g => mem_stageOneGL_union_reflCell12GL_iff_mul_unitriangularUnit g)

omit [IsTopologicalRing F] in
private theorem mem_univ_iff_apply_mem_univ
    (R : (Matrix (Fin 3) (Fin 3) F)ˣ ≃ₜ (Matrix (Fin 3) (Fin 3) F)ˣ) (x : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    x ∈ (Set.univ : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ↔ R x ∈ Set.univ :=
  ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_univ _⟩

private theorem mem_univ_iff_lawHomeo :
    ∀ i : RootIndex × F, ∀ g : (Matrix (Fin 3) (Fin 3) F)ˣ,
      g ∈ (Set.univ : Set (Matrix (Fin 3) (Fin 3) F)ˣ) ↔ lawHomeo i g ∈ Set.univ :=
  fun i g => mem_univ_iff_apply_mem_univ (lawHomeo i) g

variable [ContinuousInv₀ F] [T2Space F]
  [LocallyCompactSpace (Matrix (Fin 3) (Fin 3) F)ˣ]
  [TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) F)ˣ]

private theorem eq_zero_of_laws_of_anti (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (D₃ : BallData (F × F × F)) (hc₃ : IsCompact (D₃.ref : Set (F × F × F)))
    (hκ : D₃.IsAdmissibleAut swapAB)
    (D₅ : BallData ((F × F × F) × (F × F))) (hc₅ : IsCompact (D₅.ref : Set ((F × F × F) × (F × F))))
    (hP₁ : D₅.IsAdmissibleAut perm123) (hP₂ : D₅.IsAdmissibleAut perm132)
    (D₆ : BallData ((F × F × F) × (F × F × F)))
    (hc₆ : IsCompact (D₆.ref : Set ((F × F × F) × (F × F × F)))) (hP : D₆.IsAdmissibleAut bigPerm)
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × F, ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      Λ (rootCoeff χ i • comapHomeomorph (lawHomeo i) φ) = Λ φ)
    (hanti : ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      Λ (comapHomeomorph involutionHomeomorph φ) = -Λ φ) :
    Λ = 0 := by

  have h₀ : Descent.VanishesOn Λ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero isOpen_bigCellGL bigCellGL_subset_self isClosed_piece_bigCellGL Λ
      ((vanishesOn_empty Λ).of_eq_diff bigCellGL_eq_diff_empty) lawHomeo mem_bigCellGL_iff_lawHomeo
      mem_bigCellGL_iff_lawHomeo (rootCoeff χ) hlaw involutionHomeomorph
      mem_bigCellGL_iff_involutionUnit mem_bigCellGL_iff_involutionUnit hanti
      (fun E hE hEa => bigCell_kill hF hY hYc χ hχ D₆ hc₆ hP mem_bigCellGL_iff_lawHomeo
        mem_bigCellGL_iff_involutionUnit E hE hEa)

  have h₁ : Descent.VanishesOn Λ (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero isOpen_bigCellGL_union_cycleCell123GL cycleCell123GL_subset_union
      isClosed_piece_cycleCell123GL Λ (h₀.of_eq_diff cycleCell123GL_eq_diff_bigCellGL) lawHomeo
      mem_bigCellGL_union_cycleCell123GL_iff_lawHomeo mem_cycleCell123GL_iff_lawHomeo (rootCoeff χ)
      hlaw involutionHomeomorph mem_bigCellGL_union_cycleCell123GL_iff_involutionUnit
      mem_cycleCell123GL_iff_involutionUnit hanti
      (fun E hE hEa => cycleCell123_kill hF hY hYc χ hχ1 hχ D₅ hc₅ hP₁
        mem_cycleCell123GL_iff_lawHomeo mem_cycleCell123GL_iff_involutionUnit E hE hEa)

  have h₂ : Descent.VanishesOn Λ (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero isOpen_stageOneGL cycleCell132GL_subset_stageOneGL
      isClosed_piece_cycleCell132GL Λ (h₁.of_eq_diff cycleCell132GL_eq_diff_union) lawHomeo
      mem_stageOneGL_iff_lawHomeo mem_cycleCell132GL_iff_lawHomeo (rootCoeff χ) hlaw
      involutionHomeomorph mem_stageOneGL_iff_involutionUnit mem_cycleCell132GL_iff_involutionUnit
      hanti
      (fun E hE hEa => cycleCell132_kill hF hY hYc χ hχ1 hχ D₅ hc₅ hP₂
        mem_cycleCell132GL_iff_lawHomeo mem_cycleCell132GL_iff_involutionUnit E hE hEa)

  have h₃ : Descent.VanishesOn Λ (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_stageOneGL_union_reflCell12GL reflCell12GL_subset_union
      isClosed_piece_reflCell12GL Λ (h₂.of_eq_diff reflCell12GL_eq_diff_stageOneGL) lawHomeo
      mem_stageOneGL_union_reflCell12GL_iff_lawHomeo mem_reflCell12GL_iff_lawHomeo (rootCoeff χ)
      hlaw
      (fun E hE => reflCell12_kill hF hY hYc χ hχ1 mem_reflCell12GL_iff_lawHomeo E hE)

  have h₄ : Descent.VanishesOn Λ (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_stageTwoGL reflCell23GL_subset_stageTwoGL
      isClosed_piece_reflCell23GL Λ (h₃.of_eq_diff reflCell23GL_eq_diff_union) lawHomeo
      mem_stageTwoGL_iff_lawHomeo mem_reflCell23GL_iff_lawHomeo (rootCoeff χ) hlaw
      (fun E hE => reflCell23_kill hF hY hYc χ hχ1 mem_reflCell23GL_iff_lawHomeo E hE)

  have h₅ : Descent.VanishesOn Λ (Set.univ : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero isOpen_univ (Set.subset_univ _) isClosed_piece_borelCellGL Λ
      (h₄.of_eq_diff borelCellGL_eq_univ_diff) lawHomeo mem_univ_iff_lawHomeo
      mem_borelCellGL_iff_lawHomeo (rootCoeff χ) hlaw involutionHomeomorph
      (mem_univ_iff_apply_mem_univ involutionHomeomorph) mem_borelCellGL_iff_involutionUnit hanti
      (fun E hE hEa => borelCell_kill hF hY hYc χ hχ1 hχ D₃ hc₃ hκ mem_borelCellGL_iff_lawHomeo
        mem_borelCellGL_iff_involutionUnit E hE hEa)
  exact LinearMap.ext fun φ => apply_eq_zero_of_vanishesOn_univ Λ h₅ φ

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

namespace BruhatCellsGL3

open Topology

section Opposite

variable {M : Type*} [TopologicalSpace M]

private theorem totallyDisconnectedSpace_mulOpposite [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mᵐᵒᵖ :=
  (MulOpposite.opHomeomorph : M ≃ₜ Mᵐᵒᵖ).symm.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end Opposite
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Units

variable {M : Type*} [Monoid M] [TopologicalSpace M]

private theorem totallyDisconnectedSpace_units [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mˣ :=
  haveI : TotallyDisconnectedSpace Mᵐᵒᵖ := totallyDisconnectedSpace_mulOpposite
  (Units.isEmbedding_embedProduct : IsEmbedding (Units.embedProduct M)).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end Units
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section MatrixSpace

variable {R : Type*} [TopologicalSpace R]

private theorem locallyCompactSpace_matrix [LocallyCompactSpace R] : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) R) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → R))

private theorem totallyDisconnectedSpace_matrix [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) R) :=
  inferInstanceAs (TotallyDisconnectedSpace (Fin 3 → Fin 3 → R))

end MatrixSpace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section GeneralLinear

variable {F : Type*} [Field F] [TopologicalSpace F]

private theorem totallyDisconnectedSpace_generalLinear [TotallyDisconnectedSpace F] :
    TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) F)ˣ :=
  haveI : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) F) := totallyDisconnectedSpace_matrix
  totallyDisconnectedSpace_units

private theorem locallyCompactSpace_generalLinear [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] :
    LocallyCompactSpace (Matrix (Fin 3) (Fin 3) F)ˣ :=
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) F) := locallyCompactSpace_matrix
  inferInstance

end GeneralLinear
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end BruhatCellsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatSpace SchwartzBruhatIntegral SchwartzBruhatIntegral.BallData BruhatCellsGL3
open LanglandsTunnell.TateLocal WhittakerCoinvariantsGL3.Descent
open IsDedekindDomain NumberField

namespace WhittakerCoinvariantsGL3

section Products

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] (D : BallData F)
  (hc : IsCompact (D.ref : Set F))

private def ballData₂ : BallData (F × F) :=
  D.prod hc D hc

private theorem isCompact_ref_ballData₂ :
    IsCompact (((ballData₂ D hc).ref : AddSubgroup (F × F)) : Set (F × F)) :=
  BallData.isCompact_ref_prod _ _ _ _

private theorem ballData₂_ref : (ballData₂ D hc).ref = D.ref.prod D.ref :=
  rfl

private def ballData₃ : BallData (F × F × F) :=
  D.prod hc (ballData₂ D hc) (isCompact_ref_ballData₂ D hc)

private theorem isCompact_ref_ballData₃ :
    IsCompact (((ballData₃ D hc).ref : AddSubgroup (F × F × F)) : Set (F × F × F)) :=
  BallData.isCompact_ref_prod _ _ _ _

private theorem ballData₃_ref : (ballData₃ D hc).ref = D.ref.prod (ballData₂ D hc).ref :=
  rfl

private def ballData₅ : BallData ((F × F × F) × (F × F)) :=
  (ballData₃ D hc).prod (isCompact_ref_ballData₃ D hc) (ballData₂ D hc)
    (isCompact_ref_ballData₂ D hc)

private theorem isCompact_ref_ballData₅ :
    IsCompact (((ballData₅ D hc).ref : AddSubgroup ((F × F × F) × (F × F))) :
      Set ((F × F × F) × (F × F))) :=
  BallData.isCompact_ref_prod _ _ _ _

private def ballData₆ : BallData ((F × F × F) × (F × F × F)) :=
  (ballData₃ D hc).prod (isCompact_ref_ballData₃ D hc) (ballData₃ D hc)
    (isCompact_ref_ballData₃ D hc)

private theorem isCompact_ref_ballData₆ :
    IsCompact (((ballData₆ D hc).ref : AddSubgroup ((F × F × F) × (F × F × F))) :
      Set ((F × F × F) × (F × F × F))) :=
  BallData.isCompact_ref_prod _ _ _ _

private theorem isAdmissibleAut_swapAB : (ballData₃ D hc).IsAdmissibleAut swapAB := by
  refine isAdmissibleAut_prod_of_forall D hc (ballData₂ D hc) (isCompact_ref_ballData₂ D hc) swapAB
    (by show Continuous fun k : F × F × F => (k.2.1, k.1, k.2.2); fun_prop)
    (by show Continuous fun k : F × F × F => (k.2.1, k.1, k.2.2); fun_prop)
    (fun x => ?_)
  obtain ⟨a, b, c⟩ := x
  show (b ∈ D.ref ∧ (a, c) ∈ (ballData₂ D hc).ref) ↔ (a ∈ D.ref ∧ (b, c) ∈ (ballData₂ D hc).ref)
  simp only [ballData₂_ref, AddSubgroup.mem_prod]
  tauto

private theorem isAdmissibleAut_perm123 : (ballData₅ D hc).IsAdmissibleAut perm123 := by
  refine isAdmissibleAut_prod_of_forall (ballData₃ D hc) (isCompact_ref_ballData₃ D hc) (ballData₂ D hc)
    (isCompact_ref_ballData₂ D hc) perm123
    (by
      show Continuous fun k : (F × F × F) × (F × F) => ((k.2.1, k.1.2.1, k.2.2), (k.1.1, k.1.2.2))
      fun_prop)
    (by
      show Continuous fun k : (F × F × F) × (F × F) => ((k.2.1, k.1.2.1, k.2.2), (k.1.1, k.1.2.2))
      fun_prop)
    (fun x => ?_)
  obtain ⟨⟨a, b, c⟩, q, r⟩ := x
  show ((q, b, r) ∈ (ballData₃ D hc).ref ∧ (a, c) ∈ (ballData₂ D hc).ref) ↔
    ((a, b, c) ∈ (ballData₃ D hc).ref ∧ (q, r) ∈ (ballData₂ D hc).ref)
  simp only [ballData₃_ref, ballData₂_ref, AddSubgroup.mem_prod]
  tauto

private theorem isAdmissibleAut_perm132 : (ballData₅ D hc).IsAdmissibleAut perm132 := by
  refine isAdmissibleAut_prod_of_forall (ballData₃ D hc) (isCompact_ref_ballData₃ D hc) (ballData₂ D hc)
    (isCompact_ref_ballData₂ D hc) perm132
    (by
      show Continuous fun k : (F × F × F) × (F × F) => ((k.1.1, k.2.1, k.2.2), (k.1.2.1, k.1.2.2))
      fun_prop)
    (by
      show Continuous fun k : (F × F × F) × (F × F) => ((k.1.1, k.2.1, k.2.2), (k.1.2.1, k.1.2.2))
      fun_prop)
    (fun x => ?_)
  obtain ⟨⟨a, b, c⟩, p, r⟩ := x
  show ((a, p, r) ∈ (ballData₃ D hc).ref ∧ (b, c) ∈ (ballData₂ D hc).ref) ↔
    ((a, b, c) ∈ (ballData₃ D hc).ref ∧ (p, r) ∈ (ballData₂ D hc).ref)
  simp only [ballData₃_ref, ballData₂_ref, AddSubgroup.mem_prod]
  tauto

private theorem isAdmissibleAut_bigPerm : (ballData₆ D hc).IsAdmissibleAut bigPerm := by
  refine isAdmissibleAut_prod_of_forall (ballData₃ D hc) (isCompact_ref_ballData₃ D hc) (ballData₃ D hc)
    (isCompact_ref_ballData₃ D hc) bigPerm
    (by
      show Continuous fun k : (F × F × F) × (F × F × F) =>
        ((k.2.2.1, k.2.1, k.2.2.2), (k.1.2.1, k.1.1, k.1.2.2))
      fun_prop)
    (by
      show Continuous fun k : (F × F × F) × (F × F × F) =>
        ((k.2.2.1, k.2.1, k.2.2.2), (k.1.2.1, k.1.1, k.1.2.2))
      fun_prop)
    (fun x => ?_)
  obtain ⟨⟨a, b, c⟩, p, q, r⟩ := x
  show ((q, p, r) ∈ (ballData₃ D hc).ref ∧ (b, a, c) ∈ (ballData₃ D hc).ref) ↔
    ((a, b, c) ∈ (ballData₃ D hc).ref ∧ (p, q, r) ∈ (ballData₃ D hc).ref)
  simp only [ballData₃_ref, ballData₂_ref, AddSubgroup.mem_prod]
  tauto

include D hc in

private theorem eq_zero_of_laws_of_anti_of_ballData [T2Space F] [ContinuousInv₀ F]
    [LocallyCompactSpace (Matrix (Fin 3) (Fin 3) F)ˣ]
    [TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) F)ˣ]
    (hF : HasClopenBasis F) (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ1 : χ ≠ 1) (hχ : IsLocallyConstant fun x : F => χ x)
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × F, ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      Λ (rootCoeff χ i • comapHomeomorph (lawHomeo i) φ) = Λ φ)
    (hanti : ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      Λ (comapHomeomorph involutionHomeomorph φ) = -Λ φ) :
    Λ = 0 :=
  eq_zero_of_laws_of_anti hF hY hYc χ hχ1 hχ (ballData₃ D hc) (isCompact_ref_ballData₃ D hc)
    (isAdmissibleAut_swapAB D hc) (ballData₅ D hc) (isCompact_ref_ballData₅ D hc)
    (isAdmissibleAut_perm123 D hc) (isAdmissibleAut_perm132 D hc) (ballData₆ D hc)
    (isCompact_ref_ballData₆ D hc) (isAdmissibleAut_bigPerm D hc) Λ hlaw hanti

end Products
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem locallyCompactSpace_localField : LocallyCompactSpace (v.adicCompletion ℚ) :=
  (isCompact_integerSubgroup v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_integerSubgroup v).mem_nhds (zero_mem (integerSubgroup v)))

private theorem eq_zero_of_laws_of_anti_local (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ1 : ψ ≠ 1)
    (hψ : IsLocallyConstant fun x : v.adicCompletion ℚ => ψ x)
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × v.adicCompletion ℚ,
      ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
        Λ (rootCoeff ψ i • comapHomeomorph (lawHomeo i) φ) = Λ φ)
    (hanti : ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
      Λ (comapHomeomorph involutionHomeomorph φ) = -Λ φ) :
    Λ = 0 := by
  haveI : LocallyCompactSpace (v.adicCompletion ℚ) := locallyCompactSpace_localField v
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ :=
    locallyCompactSpace_generalLinear
  haveI : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ :=
    totallyDisconnectedSpace_generalLinear
  exact eq_zero_of_laws_of_anti_of_ballData (localBallData v) (isCompact_ref_localBallData v)
    (hasClopenBasis_localField v) (hasClopenBasis_torus v) (exists_isClopen_isCompact_mem_torus v)
    ψ hψ1 hψ Λ hlaw hanti

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatSpace SchwartzBruhatIntegral SchwartzBruhatIntegral.BallData BruhatCellsGL3
open LanglandsTunnell.TateLocal WhittakerCoinvariantsGL3.Descent
open IsDedekindDomain NumberField

namespace WhittakerCoinvariantsGL3

section Axes

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def bigAxis : F →+ (F × F × F) × (F × F × F) :=
  (AddMonoidHom.inl (F × F × F) (F × F × F)).comp
    ((AddMonoidHom.inr F (F × F)).comp (AddMonoidHom.inl F F))

omit [IsTopologicalRing F] in
private theorem continuous_bigAxis : Continuous (bigAxis : F → (F × F × F) × (F × F × F)) := by
  show Continuous fun s : F => (((0 : F), s, (0 : F)), (0 : F × F × F))
  fun_prop

private theorem bigCell_wild_rel (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (g : (F × F × F) × (F × F × F) → ℂ)
    (s : F) :
    χ s • (fun x => g (x + bigAxis s)) - g =
      (bigCellOps χ (RootIndex.left23, s)).fibreRelation t g := by
  funext k
  obtain ⟨⟨a, b, c⟩, p, q, r⟩ := k
  have e : (((a, b, c), (p, q, r)) : (F × F × F) × (F × F × F)) + bigAxis s =
      ((a, b + s, c), (p, q, r)) := by
    show (((a, b, c), (p, q, r)) : (F × F × F) × (F × F × F)) + (((0 : F), s, (0 : F)), 0) = _
    ext <;> simp
  show χ s * g (((a, b, c), (p, q, r)) + bigAxis s) - g ((a, b, c), (p, q, r)) =
    χ s * g ((a, b + s, c), (p, q, r)) - g ((a, b, c), (p, q, r))
  rw [e]

private def borelAxis : F →+ F × F × F :=
  (AddMonoidHom.inr F (F × F)).comp (AddMonoidHom.inl F F)

omit [IsTopologicalRing F] in
private theorem continuous_borelAxis : Continuous (borelAxis : F → F × F × F) := by
  show Continuous fun s : F => ((0 : F), s, (0 : F))
  fun_prop

private theorem borel_wild_rel (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (g : F × F × F → ℂ) (s : F) :
    χ s • (fun x => g (x + borelAxis s)) - g =
      (borelOps χ (RootIndex.left23, s)).fibreRelation t g := by
  funext k
  obtain ⟨a, b, c⟩ := k
  have e : ((a, b, c) : F × F × F) + borelAxis s = (a, b + s, c) := by
    show ((a, b, c) : F × F × F) + ((0 : F), s, (0 : F)) = _
    ext <;> simp
  show χ s * g ((a, b, c) + borelAxis s) - g (a, b, c) = χ s * g (a, b + s, c) - g (a, b, c)
  rw [e]

private def cycleAxis : F →+ (F × F × F) × (F × F) :=
  (AddMonoidHom.inr (F × F × F) (F × F)).comp (AddMonoidHom.inl F F)

omit [IsTopologicalRing F] in
private theorem continuous_cycleAxis : Continuous (cycleAxis : F → (F × F × F) × (F × F)) := by
  show Continuous fun s : F => ((0 : F × F × F), s, (0 : F))
  fun_prop

private theorem cycle123_wild_rel (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (g : (F × F × F) × (F × F) → ℂ)
    (s : F) :
    χ s • (fun x => g (x + cycleAxis s)) - g =
      (cycle123Ops χ (RootIndex.right23, s)).fibreRelation t g := by
  funext k
  obtain ⟨⟨a, b, c⟩, q, r⟩ := k
  have e : (((a, b, c), (q, r)) : (F × F × F) × (F × F)) + cycleAxis s =
      ((a, b, c), (q + s, r)) := by
    show (((a, b, c), (q, r)) : (F × F × F) × (F × F)) + ((0 : F × F × F), s, (0 : F)) = _
    ext <;> simp
  show χ s * g (((a, b, c), (q, r)) + cycleAxis s) - g ((a, b, c), (q, r)) =
    χ s * g ((a, b, c), (q + s, r)) - g ((a, b, c), (q, r))
  rw [e]

private theorem cycle132_wild_rel (χ : AddChar F ℂ) (t : Fˣ × Fˣ × Fˣ) (g : (F × F × F) × (F × F) → ℂ)
    (s : F) :
    χ s • (fun x => g (x + cycleAxis s)) - g =
      (cycle132Ops χ (RootIndex.right12, s)).fibreRelation t g := by
  funext k
  obtain ⟨⟨a, b, c⟩, p, r⟩ := k
  have e : (((a, b, c), (p, r)) : (F × F × F) × (F × F)) + cycleAxis s =
      ((a, b, c), (p + s, r)) := by
    show (((a, b, c), (p, r)) : (F × F × F) × (F × F)) + ((0 : F × F × F), s, (0 : F)) = _
    ext <;> simp
  show χ s * g (((a, b, c), (p, r)) + cycleAxis s) - g ((a, b, c), (p, r)) =
    χ s * g ((a, b, c), (p + s, r)) - g ((a, b, c), (p, r))
  rw [e]

end Axes
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Dead

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]

private theorem bigCell_apply_eq_zero_of_not_isLocallyConstant (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F × F)))
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F)),
      T ((bigCellOps χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (bigCellOps χ i).toLinMid)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F × F) => x.2.1)
    (fun i => (bigCellOps χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (bigCellHomeo i) (bigCellHomeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (bigCellHomeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (bigCellOps χ) hV hVc ht
      (D.mem_of_not_isLocallyConstant χ hχ bigAxis continuous_bigAxis
        (fun g hg s => by
          rw [bigCell_wild_rel χ t g s]
          exact fibreRelation_mem_fibreSpan (bigCellOps χ) t (RootIndex.left23, s) hg)
        (isSchwartzBruhat_fibreMid hf t))

private theorem cycle123_apply_eq_zero_of_not_isLocallyConstant (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F)))
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      T ((cycle123Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (cycle123Ops χ i).toLinMid)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1) (fun i => (cycle123Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (cycle123Homeo i) (cycle123Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (cycle123Homeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (cycle123Ops χ) hV hVc ht
      (D.mem_of_not_isLocallyConstant χ hχ cycleAxis continuous_cycleAxis
        (fun g hg s => by
          rw [cycle123_wild_rel χ t g s]
          exact fibreRelation_mem_fibreSpan (cycle123Ops χ) t (RootIndex.right23, s) hg)
        (isSchwartzBruhat_fibreMid hf t))

private theorem cycle132_apply_eq_zero_of_not_isLocallyConstant (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F)))
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F)),
      T ((cycle132Ops χ i).toLinMid f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (cycle132Ops χ i).toLinMid)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre
    (fun x : (F × F × F) × (Fˣ × Fˣ × Fˣ) × (F × F) => x.2.1) (fun i => (cycle132Ops χ i).toLinMid)
    (sbSubmodule _) (by fun_prop) hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem (by fun_prop) (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLinMid_opOfMapMid_mem (rootCoeff χ i) (cycle132Homeo i) (cycle132Homeo_torus i) g hg
  · intro i V _ g _
    exact toLinMid_opOfMapMid_indicator (rootCoeff χ i) (cycle132Homeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_mid_eq (cycle132Ops χ) hV hVc ht
      (D.mem_of_not_isLocallyConstant χ hχ cycleAxis continuous_cycleAxis
        (fun g hg s => by
          rw [cycle132_wild_rel χ t g s]
          exact fibreRelation_mem_fibreSpan (cycle132Ops χ) t (RootIndex.right12, s) hg)
        (isSchwartzBruhat_fibreMid hf t))

private theorem borel_apply_eq_zero_of_not_isLocallyConstant (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x) (D : BallData (F × F × F))
    (T : ((F × F × F) × (Fˣ × Fˣ × Fˣ) → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ f ∈ sbSubmodule ((F × F × F) × (Fˣ × Fˣ × Fˣ)),
      T ((borelOps χ i).toLin f) = T f)
    {f : (F × F × F) × (Fˣ × Fˣ × Fˣ) → ℂ} (hf : IsSchwartzBruhat f) : T f = 0 := by
  refine Localisation.apply_eq_zero_of_mem_coinvariants (fun i => (borelOps χ i).toLin)
    (sbSubmodule _) T hT ?_
  refine Localisation.mem_coinvariants_of_forall_fibre Prod.snd (fun i => (borelOps χ i).toLin)
    (sbSubmodule _) continuous_snd hY (fun g hg => (mem_sbSubmodule.mp hg).1)
    (fun g hg => (mem_sbSubmodule.mp hg).2) ?_ ?_ ?_ (mem_sbSubmodule.mpr hf) ?_
  · intro g hg V hV
    exact indicator_preimage_mem continuous_snd (mem_sbSubmodule.mp hg) hV
  · intro i g hg
    exact toLin_opOfMapLast_mem (rootCoeff χ i) (borelHomeo i) (borelHomeo_torus i) g hg
  · intro i V _ g _
    exact toLin_opOfMapLast_indicator (rootCoeff χ i) (borelHomeo_torus i) V g
  · intro t _
    obtain ⟨V, hV, hVc, ht⟩ := hYc t
    exact exists_mem_coinvariants_forall_snd_eq (borelOps χ) hV hVc ht
      (D.mem_of_not_isLocallyConstant χ hχ borelAxis continuous_borelAxis
        (fun g hg s => by
          rw [borel_wild_rel χ t g s]
          exact fibreRelation_mem_fibreSpan (borelOps χ) t (RootIndex.left23, s) hg)
        (isSchwartzBruhat_fibreLast hf t))

end Dead
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section WildGroup

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
  [T2Space F]

private theorem bigCell_kill_wild (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F × F)))
    (hC : ∀ i g, g ∈ bigCellGL ↔ lawHomeo i g ∈ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ bigCellGL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E bigCellHomeomorph (fun i => (lawHomeo i).subtype (hC i)) bigCellHomeo
    (bigCell_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => bigCell_apply_eq_zero_of_not_isLocallyConstant hY hYc χ hχ D T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (bigCellHomeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

private theorem cycleCell123_kill_wild (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F)))
    (hC : ∀ i g, g ∈ cycleCell123GL ↔
      lawHomeo i g ∈ (cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell123GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E cycleCell123Homeomorph (fun i => (lawHomeo i).subtype (hC i)) cycle123Homeo
    (cycleCell123_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => cycle123_apply_eq_zero_of_not_isLocallyConstant hY hYc χ hχ D T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (cycle123Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

private theorem cycleCell132_kill_wild (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x)
    (D : BallData ((F × F × F) × (F × F)))
    (hC : ∀ i g, g ∈ cycleCell132GL ↔
      lawHomeo i g ∈ (cycleCell132GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ cycleCell132GL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E cycleCell132Homeomorph (fun i => (lawHomeo i).subtype (hC i)) cycle132Homeo
    (cycleCell132_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => cycle132_apply_eq_zero_of_not_isLocallyConstant hY hYc χ hχ D T
      (fun i g hg =>
        (congrArg T (toLinMid_opOfMapMid (rootCoeff χ i) (cycle132Homeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

private theorem borelCell_kill_wild (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x) (D : BallData (F × F × F))
    (hC : ∀ i g, g ∈ borelCellGL ↔ lawHomeo i g ∈ (borelCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ))
    (E : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL} →ₗ[ℂ] ℂ)
    (hE : ∀ i, ∀ h : testSpace {g : (Matrix (Fin 3) (Fin 3) F)ˣ // g ∈ borelCellGL},
      E (rootCoeff χ i • comapHomeomorph ((lawHomeo i).subtype (hC i)) h) = E h) :
    E = 0 :=
  eq_zero_of_model' E borelCellHomeomorph (fun i => (lawHomeo i).subtype (hC i)) borelHomeo
    (borelCell_conj hC) (rootCoeff χ) hE
    (fun T hT _ hf => borel_apply_eq_zero_of_not_isLocallyConstant hY hYc χ hχ D T
      (fun i g hg =>
        (congrArg T (toLin_opOfMapLast (rootCoeff χ i) (borelHomeo_torus i) g)).trans
          (hT i g (mem_sbSubmodule.mp hg))) hf)

omit [IsTopologicalRing F] [ContinuousInv₀ F] [T2Space F] in

private theorem ne_one_of_not_isLocallyConstant (χ : AddChar F ℂ)
    (hχ : ¬ IsLocallyConstant fun x : F => χ x) : χ ≠ 1 := by
  rintro rfl
  exact hχ (IsLocallyConstant.of_constant _ fun _ _ => rfl)

variable [LocallyCompactSpace (Matrix (Fin 3) (Fin 3) F)ˣ]
  [TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) F)ˣ]

private theorem eq_zero_of_laws_of_not_isLocallyConstant (hF : HasClopenBasis F)
    (hY : HasClopenBasis (Fˣ × Fˣ × Fˣ))
    (hYc : ∀ t : Fˣ × Fˣ × Fˣ, ∃ V : Set (Fˣ × Fˣ × Fˣ), IsClopen V ∧ IsCompact V ∧ t ∈ V)
    (χ : AddChar F ℂ) (hχ : ¬ IsLocallyConstant fun x : F => χ x) (D₃ : BallData (F × F × F))
    (D₅ : BallData ((F × F × F) × (F × F))) (D₆ : BallData ((F × F × F) × (F × F × F)))
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × F, ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      Λ (rootCoeff χ i • comapHomeomorph (lawHomeo i) φ) = Λ φ) :
    Λ = 0 := by
  have hχ1 : χ ≠ 1 := ne_one_of_not_isLocallyConstant χ hχ
  have h₀ : Descent.VanishesOn Λ (bigCellGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_bigCellGL bigCellGL_subset_self isClosed_piece_bigCellGL Λ
      ((vanishesOn_empty Λ).of_eq_diff bigCellGL_eq_diff_empty) lawHomeo mem_bigCellGL_iff_lawHomeo
      mem_bigCellGL_iff_lawHomeo (rootCoeff χ) hlaw
      (fun E hE => bigCell_kill_wild hY hYc χ hχ D₆ mem_bigCellGL_iff_lawHomeo E hE)
  have h₁ : Descent.VanishesOn Λ (bigCellGL ∪ cycleCell123GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_bigCellGL_union_cycleCell123GL cycleCell123GL_subset_union
      isClosed_piece_cycleCell123GL Λ (h₀.of_eq_diff cycleCell123GL_eq_diff_bigCellGL) lawHomeo
      mem_bigCellGL_union_cycleCell123GL_iff_lawHomeo mem_cycleCell123GL_iff_lawHomeo (rootCoeff χ)
      hlaw
      (fun E hE => cycleCell123_kill_wild hY hYc χ hχ D₅ mem_cycleCell123GL_iff_lawHomeo E hE)
  have h₂ : Descent.VanishesOn Λ (stageOneGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_stageOneGL cycleCell132GL_subset_stageOneGL
      isClosed_piece_cycleCell132GL Λ (h₁.of_eq_diff cycleCell132GL_eq_diff_union) lawHomeo
      mem_stageOneGL_iff_lawHomeo mem_cycleCell132GL_iff_lawHomeo (rootCoeff χ) hlaw
      (fun E hE => cycleCell132_kill_wild hY hYc χ hχ D₅ mem_cycleCell132GL_iff_lawHomeo E hE)
  have h₃ : Descent.VanishesOn Λ (stageOneGL ∪ reflCell12GL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_stageOneGL_union_reflCell12GL reflCell12GL_subset_union
      isClosed_piece_reflCell12GL Λ (h₂.of_eq_diff reflCell12GL_eq_diff_stageOneGL) lawHomeo
      mem_stageOneGL_union_reflCell12GL_iff_lawHomeo mem_reflCell12GL_iff_lawHomeo (rootCoeff χ)
      hlaw
      (fun E hE => reflCell12_kill hF hY hYc χ hχ1 mem_reflCell12GL_iff_lawHomeo E hE)
  have h₄ : Descent.VanishesOn Λ (stageTwoGL : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_stageTwoGL reflCell23GL_subset_stageTwoGL
      isClosed_piece_reflCell23GL Λ (h₃.of_eq_diff reflCell23GL_eq_diff_union) lawHomeo
      mem_stageTwoGL_iff_lawHomeo mem_reflCell23GL_iff_lawHomeo (rootCoeff χ) hlaw
      (fun E hE => reflCell23_kill hF hY hYc χ hχ1 mem_reflCell23GL_iff_lawHomeo E hE)
  have h₅ : Descent.VanishesOn Λ (Set.univ : Set (Matrix (Fin 3) (Fin 3) F)ˣ) :=
    vanishesOn_of_forall_eq_zero' isOpen_univ (Set.subset_univ _) isClosed_piece_borelCellGL Λ
      (h₄.of_eq_diff borelCellGL_eq_univ_diff) lawHomeo mem_univ_iff_lawHomeo
      mem_borelCellGL_iff_lawHomeo (rootCoeff χ) hlaw
      (fun E hE => borelCell_kill_wild hY hYc χ hχ D₃ mem_borelCellGL_iff_lawHomeo E hE)
  exact LinearMap.ext fun φ => apply_eq_zero_of_vanishesOn_univ Λ h₅ φ

end WildGroup
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem eq_zero_of_laws_of_not_isLocallyConstant_local (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ : ¬ IsLocallyConstant fun x : v.adicCompletion ℚ => ψ x)
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × v.adicCompletion ℚ,
      ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
        Λ (rootCoeff ψ i • comapHomeomorph (lawHomeo i) φ) = Λ φ) :
    Λ = 0 := by
  haveI : LocallyCompactSpace (v.adicCompletion ℚ) := locallyCompactSpace_localField v
  haveI : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ :=
    locallyCompactSpace_generalLinear
  haveI : TotallyDisconnectedSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ :=
    totallyDisconnectedSpace_generalLinear
  exact eq_zero_of_laws_of_not_isLocallyConstant (hasClopenBasis_localField v)
    (hasClopenBasis_torus v) (exists_isClopen_isCompact_mem_torus v) ψ hψ
    (ballData₃ (localBallData v) (isCompact_ref_localBallData v))
    (ballData₅ (localBallData v) (isCompact_ref_localBallData v))
    (ballData₆ (localBallData v) (isCompact_ref_localBallData v)) Λ hlaw

private theorem eq_zero_of_laws_of_anti_local' (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ1 : ψ ≠ 1)
    (Λ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ →ₗ[ℂ] ℂ)
    (hlaw : ∀ i : RootIndex × v.adicCompletion ℚ,
      ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
        Λ (rootCoeff ψ i • comapHomeomorph (lawHomeo i) φ) = Λ φ)
    (hanti : ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
      Λ (comapHomeomorph involutionHomeomorph φ) = -Λ φ) :
    Λ = 0 := by
  by_cases hψ : IsLocallyConstant fun x : v.adicCompletion ℚ => ψ x
  · exact eq_zero_of_laws_of_anti_local v ψ hψ1 hψ Λ hlaw hanti
  · exact eq_zero_of_laws_of_not_isLocallyConstant_local v ψ hψ Λ hlaw

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

noncomputable section

open SchwartzBruhatSpace SchwartzBruhatIntegral BruhatCellsGL3
open IsDedekindDomain NumberField

namespace WhittakerCoinvariantsGL3

section Exchange

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

private def exchange : RootIndex × F → RootIndex × F
  | (.left12, s) => (.right23, s)
  | (.left23, s) => (.right12, s)
  | (.left13, s) => (.right13, s)
  | (.right12, s) => (.left23, s)
  | (.right23, s) => (.left12, s)
  | (.right13, s) => (.left13, s)

omit [TopologicalSpace F] [IsTopologicalRing F] in

private theorem rootCoeff_exchange (χ : AddChar F ℂ) (i : RootIndex × F) :
    rootCoeff χ (exchange i) = rootCoeff χ i := by
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i <;> rfl

private theorem lawHomeo_involutionHomeomorph (i : RootIndex × F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ) :
    lawHomeo i (involutionHomeomorph g) = involutionHomeomorph (lawHomeo (exchange i) g) := by
  apply Units.ext
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · show ((lawHomeo (RootIndex.left12, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.right23, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_left12, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_right23, involution_mul]
    show unitriangular s 0 0 * _ = involution (unitriangular 0 s 0) * _
    rw [involution_unitriangular]
  · show ((lawHomeo (RootIndex.left23, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.right12, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_left23, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_right12, involution_mul]
    show unitriangular 0 s 0 * _ = involution (unitriangular s 0 0) * _
    rw [involution_unitriangular]
  · show ((lawHomeo (RootIndex.left13, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.right13, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_left13, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_right13, involution_mul]
    show unitriangular 0 0 s * _ = involution (unitriangular 0 0 s) * _
    rw [involution_unitriangular]
  · show ((lawHomeo (RootIndex.right12, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.left23, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_right12, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_left23, involution_mul]
    show _ * unitriangular s 0 0 = _ * involution (unitriangular 0 s 0)
    rw [involution_unitriangular]
  · show ((lawHomeo (RootIndex.right23, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.left12, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_right23, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_left12, involution_mul]
    show _ * unitriangular 0 s 0 = _ * involution (unitriangular s 0 0)
    rw [involution_unitriangular]
  · show ((lawHomeo (RootIndex.right13, s) (involutionHomeomorph g) : (Matrix (Fin 3) (Fin 3) F)ˣ) :
        Matrix (Fin 3) (Fin 3) F) = (involutionHomeomorph (lawHomeo (RootIndex.left13, s) g) :
          (Matrix (Fin 3) (Fin 3) F)ˣ)
    rw [val_lawHomeo_right13, val_involutionHomeomorph_apply, val_involutionHomeomorph_apply,
      val_lawHomeo_left13, involution_mul]
    show _ * unitriangular 0 0 s = _ * involution (unitriangular 0 0 s)
    rw [involution_unitriangular]

private theorem comapHomeomorph_involution_lawHomeo (i : RootIndex × F)
    (φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ) :
    comapHomeomorph involutionHomeomorph (comapHomeomorph (lawHomeo i) φ) =
      comapHomeomorph (lawHomeo (exchange i)) (comapHomeomorph involutionHomeomorph φ) := by
  apply Subtype.ext
  funext g
  show (φ : (Matrix (Fin 3) (Fin 3) F)ˣ → ℂ) (lawHomeo i (involutionHomeomorph g)) =
    (φ : (Matrix (Fin 3) (Fin 3) F)ˣ → ℂ) (involutionHomeomorph (lawHomeo (exchange i) g))
  rw [lawHomeo_involutionHomeomorph]

private theorem comapHomeomorph_involution_involution (φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ) :
    comapHomeomorph involutionHomeomorph (comapHomeomorph involutionHomeomorph φ) = φ := by
  apply Subtype.ext
  funext g
  show (φ : (Matrix (Fin 3) (Fin 3) F)ˣ → ℂ) (involutionHomeomorph (involutionHomeomorph g)) = _
  rw [involutionHomeomorph_involutionHomeomorph]

private theorem laws_of_sub (χ : AddChar F ℂ) (T : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × F, ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ,
      T (rootCoeff χ i • comapHomeomorph (lawHomeo i) φ) = T φ)
    (i : RootIndex × F) (φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ) :
    (T ∘ₗ (comapHomeomorph involutionHomeomorph).toLinearMap - T)
        (rootCoeff χ i • comapHomeomorph (lawHomeo i) φ) =
      (T ∘ₗ (comapHomeomorph involutionHomeomorph).toLinearMap - T) φ := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, hT i φ, LinearEquiv.map_smul, comapHomeomorph_involution_lawHomeo,
    ← rootCoeff_exchange χ i, hT (exchange i) (comapHomeomorph involutionHomeomorph φ)]

private theorem anti_of_sub (T : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ →ₗ[ℂ] ℂ)
    (φ : testSpace (Matrix (Fin 3) (Fin 3) F)ˣ) :
    (T ∘ₗ (comapHomeomorph involutionHomeomorph).toLinearMap - T)
        (comapHomeomorph involutionHomeomorph φ) =
      -(T ∘ₗ (comapHomeomorph involutionHomeomorph).toLinearMap - T) φ := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, comapHomeomorph_involution_involution, neg_sub]

end Exchange
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem apply_comapHomeomorph_involutionHomeomorph (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ψ ≠ 1) (T : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ →ₗ[ℂ] ℂ)
    (hT : ∀ i : RootIndex × v.adicCompletion ℚ,
      ∀ φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ,
        T (rootCoeff ψ i • comapHomeomorph (lawHomeo i) φ) = T φ)
    (φ : testSpace (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ˣ) :
    T (comapHomeomorph involutionHomeomorph φ) = T φ := by
  have h := eq_zero_of_laws_of_anti_local' v ψ hψ1
    (T ∘ₗ (comapHomeomorph involutionHomeomorph).toLinearMap - T) (laws_of_sub ψ T hT)
    (anti_of_sub T)
  have hφ := LinearMap.congr_fun h φ
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply,
    sub_eq_zero] at hφ
  exact hφ

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

section

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open SchwartzBruhatSpace SchwartzBruhatIntegral BruhatCellsGL3

namespace WhittakerCoinvariantsGL3

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem upperUnipotent3_eq_unitriangularUnit (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) = unitriangularUnit x y z :=
  rfl

private theorem longWeyl3_mul_transposeInv3_inv_mul_longWeyl3_inv (g : LocalGL3 v) :
    longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹ = involutionHomeomorph g :=
  Units.ext rfl

private theorem laws_of_left_of_right (ψ : AddChar (v.adicCompletion ℚ) ℂ) (T : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ ((upperUnipotent3 x y z)⁻¹ * g)) = ψ (x + y) * T φ)
    (hright : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ (g * upperUnipotent3 x y z)) = ψ (-(x + y)) * T φ)
    (i : RootIndex × v.adicCompletion ℚ) (θ : testSpace (LocalGL3 v)) :
    (T ∘ₗ (testSpace (LocalGL3 v)).subtype) (rootCoeff ψ i • comapHomeomorph (lawHomeo i) θ) =
      (T ∘ₗ (testSpace (LocalGL3 v)).subtype) θ := by
  have hθ : IsSchwartzBruhat (θ : LocalGL3 v → ℂ) := mem_testSpace.mp θ.2
  have hsub : ∀ n : LocalGL3 v, IsSchwartzBruhat fun g => (θ : LocalGL3 v → ℂ) (n * g) :=
    fun n => isSchwartzBruhat_comp_homeo hθ (Homeomorph.mulLeft n)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.subtype_apply,
    Submodule.coe_smul, map_smul, smul_eq_mul]
  obtain ⟨_ | _ | _ | _ | _ | _, s⟩ := i
  · have h := hleft s 0 0 _ (hsub (upperUnipotent3 s 0 0))
    simp only [mul_inv_cancel_left, add_zero] at h
    show ψ s * T (fun g => (θ : LocalGL3 v → ℂ) (upperUnipotent3 s 0 0 * g)) = T θ
    rw [h]
  · have h := hleft 0 s 0 _ (hsub (upperUnipotent3 0 s 0))
    simp only [mul_inv_cancel_left, zero_add] at h
    show ψ s * T (fun g => (θ : LocalGL3 v → ℂ) (upperUnipotent3 0 s 0 * g)) = T θ
    rw [h]
  · have h := hleft 0 0 s _ (hsub (upperUnipotent3 0 0 s))
    simp only [mul_inv_cancel_left, add_zero, AddChar.map_zero_eq_one, one_mul] at h
    show 1 * T (fun g => (θ : LocalGL3 v → ℂ) (upperUnipotent3 0 0 s * g)) = T θ
    rw [one_mul, h]
  · have h := hright s 0 0 _ hθ
    show ψ s * T (fun g => (θ : LocalGL3 v → ℂ) (g * upperUnipotent3 s 0 0)) = T θ
    rw [h, add_zero, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      one_mul]
  · have h := hright 0 s 0 _ hθ
    show ψ s * T (fun g => (θ : LocalGL3 v → ℂ) (g * upperUnipotent3 0 s 0)) = T θ
    rw [h, zero_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      one_mul]
  · have h := hright 0 0 s _ hθ
    show 1 * T (fun g => (θ : LocalGL3 v → ℂ) (g * upperUnipotent3 0 0 s)) = T θ
    rw [h, add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, one_mul]

private theorem apply_comp_conj_transpose_eq_apply_of_ne_one (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ : ψ ≠ 1) (T : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ ((upperUnipotent3 x y z)⁻¹ * g)) = ψ (x + y) * T φ)
    (hright : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ (g * upperUnipotent3 x y z)) = ψ (-(x + y)) * T φ)
    (φ : LocalGL3 v → ℂ) (hφ : IsSchwartzBruhat φ) :
    T (fun g => φ (longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹)) = T φ := by
  have e : (fun g => φ (longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹)) =
      fun g => φ (involutionHomeomorph g) :=
    funext fun g => congrArg φ (longWeyl3_mul_transposeInv3_inv_mul_longWeyl3_inv v g)
  rw [e]
  exact apply_comapHomeomorph_involutionHomeomorph v ψ hψ (T ∘ₗ (testSpace (LocalGL3 v)).subtype)
    (laws_of_left_of_right v ψ T hleft hright) ⟨φ, mem_testSpace.mpr hφ⟩

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end WhittakerCoinvariantsGL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.SchwartzBruhatIntegral P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.WhittakerCoinvariantsGL3 P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.BruhatCellsGL3"

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (_hψv : ψv ≠ 1)
    (T : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)
    (_hleft : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ ((upperUnipotent3 x y z)⁻¹ * g)) = ψv (x + y) * T φ)
    (_hright : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ (g * upperUnipotent3 x y z)) = ψv (-(x + y)) * T φ)
    (φ : LocalGL3 v → ℂ) (_hφ : IsSchwartzBruhat φ) :
    T (fun g => φ (longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹)) = T φ := by
  exact WhittakerCoinvariantsGL3.apply_comp_conj_transpose_eq_apply_of_ne_one v ψv _hψv T _hleft _hright φ
    _hφ

end S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one (solution)
