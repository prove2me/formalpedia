-- Prove2me | solution 1 for OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:32:12.158651+00:00
-- url     : https://prove2.me/submissions/29dae3e3-daef-4d5b-ab27-3ff4dbf7e319

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RankTransfer.lean:L82-L134
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer

-- ---- from OAI.Algebra.Determinantal.RankTransfer ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma exists_matrix_right_inverse {K α β : Type*} [Field K] [Fintype α] [Fintype β] [DecidableEq α]
    (A : Matrix α β K) (hA : Function.Surjective A.mulVec) :
    ∃ B : Matrix β α K, A * B = 1 := by
  classical
  choose b hb using fun i : α => hA (Pi.single i 1)
  refine ⟨fun j i => b i j, ?_⟩
  ext i j
  change (A.mulVec (b j)) i = (1 : Matrix α α K) i j
  rw [hb]
  simp [Matrix.one_apply, Pi.single_apply]

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

theorem polynomial_rank_specialize {K L σ α β : Type*}
    [Field K] [Field L] [Algebra K L] [Infinite K] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ K)) (x : σ → L)
    (hP : Function.Surjective (P.map (eval₂Hom (algebraMap K L) x)).mulVec) :
    ∃ y : σ → K,
      Function.Surjective (P.map (eval₂Hom (RingHom.id K) y)).mulVec := by
  classical
  let τ := σ ⊕ (β × α)
  let A : Matrix α β (MvPolynomial τ K) := P.map (rename Sum.inl)
  let B : Matrix β α (MvPolynomial τ K) := fun i j => X (Sum.inr (i,j))
  let p : MvPolynomial τ K := (A*B).det
  obtain ⟨b,hb⟩ := exists_matrix_right_inverse _ hP
  let z : τ → L := Sum.elim x (fun ij => b ij.1 ij.2)
  let φ : MvPolynomial τ K →+* L := eval₂Hom (algebraMap K L) z
  have hA : A.map φ = P.map (eval₂Hom (algebraMap K L) x) := by
    ext i j
    simp [A, φ, z, Matrix.map_apply, eval₂_rename, Function.comp_def]
  have hB : B.map φ = b := by
    ext i j
    change φ (X (Sum.inr (i,j))) = b i j
    exact eval₂_X _ _ _
  have hp : φ p = 1 := by
    rw [show φ p = (φ.mapMatrix (A*B)).det from RingHom.map_det φ (A*B)]
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hA, hB, hb]
    exact Matrix.det_one
  have hpn : p ≠ 0 := by
    intro h
    have : (0 : L) = 1 := by simpa only [h, map_zero] using hp
    exact zero_ne_one this
  obtain ⟨w,hw⟩ : ∃ w : τ → K, eval w p ≠ 0 := by
    by_contra h
    apply hpn
    apply MvPolynomial.funext
    intro w
    simp only [map_zero]
    exact not_not.mp (not_exists.mp h w)
  let ψ : MvPolynomial τ K →+* K := eval₂Hom (RingHom.id K) w
  have hψ : ψ p ≠ 0 := by
    exact hw
  have hu : IsUnit ((A*B).map ψ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr hψ
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  refine ⟨fun i => w (Sum.inl i), ?_⟩
  have hAL : A.map ψ = P.map (eval₂Hom (RingHom.id K) (fun i => w (Sum.inl i))) := by
    ext i j
    simp [A, ψ, Matrix.map_apply, eval₂_rename, Function.comp_def]
  intro v
  obtain ⟨t,ht⟩ := hs v
  refine ⟨(B.map ψ).mulVec t, ?_⟩
  rw [← hAL, Matrix.mulVec_mulVec]
  simpa only [Matrix.map_mul] using ht

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize := @_root_.OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize
