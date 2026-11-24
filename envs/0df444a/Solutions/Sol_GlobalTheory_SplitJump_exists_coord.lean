-- Prove2me | solution 1 for GlobalTheory.SplitJump.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:13.89886+00:00
-- url     : https://prove2.me/submissions/42986ba9-ac68-43e3-bdd1-24bd5facebb2

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
import Theorems.Thm_GlobalTheory_SplitJump_coord_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
namespace GlobalTheory.SplitJump
namespace _root_.GlobalTheory.SplitJump
theorem _root_.solution (W W' : Matrix (Fin n) (Fin n) BdR) (hWW : W * W' = 1)
    (hg : ∀ g, (Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)) *
      W.map (PD.actdR g) = W)
    (y : V ⊗[Qp] BdR) (hy : y ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) :
    ∃ k : Fin n → K, (fun i => algebraMap K BdR (k i)) =
      W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y) := by
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.DdR at hy
  have hfix : ∀ g, _root_.Formalism.WeaklyAdmissibleFiltrations.actVdR PD ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).1 hy g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  have hinv : ∀ i g, PD.actdR g ((W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i) =
      (W'.mulVec (_root_.GlobalTheory.SplitJump.coord e BdR y)) i := by
    intro i g
    set M : Matrix (Fin n) (Fin n) BdR :=
      Matrix.of fun i j => algebraMap Qp BdR (e.repr (ρ g (e j)) i)
    set σ : BdR →+* BdR := (PD.actdR g : BdR ≃ₐ[K] BdR).toRingEquiv.toRingHom
    have hW'W : W' * W = 1 := mul_eq_one_comm.1 hWW
    have hmap : W'.map σ = W' * M := by
      have h1 : W.map σ * W'.map σ = 1 := by
        rw [← Matrix.map_mul, hWW, Matrix.map_one _ (map_zero σ) (map_one σ)]
      calc W'.map σ = (W' * W) * W'.map σ := by rw [hW'W, Matrix.one_mul]
        _ = W' * (M * W.map σ) * W'.map σ := by rw [show M * W.map σ = W from hg g]
        _ = W' * M * (W.map σ * W'.map σ) := by simp only [Matrix.mul_assoc]
        _ = W' * M := by rw [h1, Matrix.mul_one]
    have hc : M.mulVec (fun j => σ (_root_.GlobalTheory.SplitJump.coord e BdR y j)) =
        _root_.GlobalTheory.SplitJump.coord e BdR y := by
      have := _root_.GlobalTheory.SplitJump.coord_act PD ρ e g y
      rw [hfix g] at this
      exact this.symm
    change σ _ = _
    rw [RingHom.map_mulVec, hmap]
    change (W' * M).mulVec (σ ∘ _root_.GlobalTheory.SplitJump.coord e BdR y) i = _
    rw [← Matrix.mulVec_mulVec]
    congr 2
  choose k hk using fun i => PD.invdR _ fun g => hinv i g
  exact ⟨k, funext hk⟩
end _root_.GlobalTheory.SplitJump
end GlobalTheory.SplitJump
