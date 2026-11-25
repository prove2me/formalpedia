-- Prove2me | solution 1 for GroundTheory.Brauer.exists_maximal_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:14.244354+00:00
-- url     : https://prove2.me/submissions/45677c7e-8b80-452e-88bb-098b785bccbe

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_isSimpleRing_of_finiteDimensional
import Theorems.Thm_GroundTheory_Brauer_isSeparable_coe_iff
import Theorems.Thm_GroundTheory_Brauer_le_centralizer_of_isMulCommutative
import Theorems.Thm_GroundTheory_Brauer_isMulCommutative_adjoin_insert
import Theorems.Thm_GroundTheory_Brauer_maximal_isMulCommutative_iff_centralizer_eq
import Theorems.Thm_GroundTheory_Brauer_centralizer_centralizer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
variable [Algebra.IsCentral K D] [FiniteDimensional K D]
namespace GroundTheory.Brauer
theorem _root_.solution :
    ∃ F : Subalgebra K D, IsMulCommutative F ∧
      Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ∧ ∀ x ∈ F, IsSeparable K x := by
  classical
  let P : ℕ → Prop := fun d ↦ ∃ F : Subalgebra K D, IsMulCommutative F ∧
    (∀ x ∈ F, IsSeparable K x) ∧ finrank K F = d
  have hbot : IsMulCommutative (⊥ : Subalgebra K D) := isMulCommutative_iff.mpr fun a b ↦ by
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp a.2
    apply Subtype.ext
    change (a : D) * b = b * a
    rw [← hk]
    exact Algebra.commutes k (b : D)
  have hP1 : P 1 := by
    refine ⟨⊥, hbot, fun x hx ↦ ?_, Subalgebra.finrank_bot⟩
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.mp hx
    exact isSeparable_algebraMap k
  have hD : 1 ≤ finrank K D := Module.finrank_pos
  obtain ⟨F, hFc, hFs, hFd⟩ := Nat.findGreatest_spec hD hP1
  refine ⟨F, hFc, (maximal_isMulCommutative_iff_centralizer_eq F).mpr ?_, hFs⟩
  refine le_antisymm (fun x hx ↦ ?_) (le_centralizer_of_isMulCommutative F)
  by_contra hxF
  set C := Subalgebra.centralizer K (F : Set D)
  let _ : DivisionRing C := divisionRingOfFiniteDimensional C
  let _ : Field F := fieldOfIsMulCommutative F
  have : IsSimpleRing F := isSimpleRing_of_finiteDimensional F
  have hFC : F ≤ C := le_centralizer_of_isMulCommutative F

  let _ : Algebra F C := RingHom.toAlgebra' (Subalgebra.inclusion hFC).toRingHom
    fun c z ↦ Subtype.ext ((Subalgebra.mem_centralizer_iff K).mp z.2 c c.2)
  have : IsScalarTower K F C := IsScalarTower.of_algebraMap_eq fun k ↦ rfl
  have : Module.Finite F C := Module.Finite.of_restrictScalars_finite K F C
  have : Algebra.IsAlgebraic F C := Algebra.IsAlgebraic.of_finite F C
  have : Algebra.IsCentral F C := ⟨fun z hz ↦ by
    have hzC : (z : D) ∈ Subalgebra.centralizer K (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val ((Subalgebra.mem_center_iff.mp hz) ⟨g, hg⟩)
    have hcc : Subalgebra.centralizer K (C : Set D) = F := centralizer_centralizer F
    rw [hcc] at hzC
    exact Algebra.mem_bot.mpr ⟨⟨z, hzC⟩, Subtype.ext rfl⟩⟩
  have hne : (⊥ : Subalgebra F C) ≠ ⊤ := by
    intro h
    have hmem : (⟨x, hx⟩ : C) ∈ (⊥ : Subalgebra F C) := h ▸ Algebra.mem_top
    obtain ⟨f, hf⟩ := Algebra.mem_bot.mp hmem
    apply hxF
    have hfx : (f : D) = x := congrArg Subtype.val hf
    exact hfx ▸ f.2

  obtain ⟨y, hyF, hysep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
  have hyC : (y : D) ∈ C := y.2
  have hyF' : (y : D) ∉ F := fun h ↦ hyF (Algebra.mem_bot.mpr ⟨⟨y, h⟩, Subtype.ext rfl⟩)
  set G := Algebra.adjoin K (insert (y : D) (F : Set D))
  have hGc : IsMulCommutative G := isMulCommutative_adjoin_insert F hyC
  have hFG : F ≤ G := fun z hz ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
  have hyG : (y : D) ∈ G := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hGC : G ≤ C := Algebra.adjoin_le (Set.insert_subset hyC fun z hz ↦ hFC hz)

  let _ : Field G := fieldOfIsMulCommutative G
  let _ : Algebra F G := (Subalgebra.inclusion hFG).toRingHom.toAlgebra
  have : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq fun k ↦ rfl
  have : Algebra.IsSeparable K F := ⟨fun z ↦ (isSeparable_coe_iff z).mp (hFs z z.2)⟩
  let yG : G := ⟨y, hyG⟩
  let ψ : G →ₐ[F] C :=
    { (Subalgebra.inclusion hGC).toRingHom with commutes' := fun f ↦ rfl }
  have hψ : Function.Injective ψ := fun a b h ↦ Subtype.ext (congrArg Subtype.val h :)
  have hyGsep : IsSeparable F yG := by
    unfold IsSeparable
    rw [← minpoly.algHom_eq ψ hψ yG]
    exact hysep
  have hyKsep : IsSeparable K yG := IsSeparable.of_algebra_isSeparable_of_isSeparable K hyGsep
  have hGsep : ∀ z ∈ G, IsSeparable K z := by
    have hle : G ≤ (separableClosure K G).toSubalgebra.map G.val := by
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · exact ⟨yG, mem_separableClosure_iff.mpr hyKsep, rfl⟩
      · intro f hf
        exact ⟨⟨f, hFG hf⟩, mem_separableClosure_iff.mpr
          ((isSeparable_coe_iff (⟨f, hFG hf⟩ : G)).mp (hFs f hf)), rfl⟩
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hle hz
    exact (isSeparable_coe_iff w).mpr (mem_separableClosure_iff.mp hw)

  have hPG : P (finrank K G) := ⟨G, hGc, hGsep, rfl⟩
  have hGD : finrank K G ≤ finrank K D := Submodule.finrank_le (Subalgebra.toSubmodule G)
  have hle := Nat.le_findGreatest hGD hPG
  have hlt : Subalgebra.toSubmodule F < Subalgebra.toSubmodule G :=
    SetLike.lt_iff_le_and_exists.mpr ⟨hFG, (y : D), hyG, hyF'⟩
  have hlt' : finrank K F < finrank K G := Submodule.finrank_lt_finrank_of_lt hlt
  omega
end GroundTheory.Brauer
