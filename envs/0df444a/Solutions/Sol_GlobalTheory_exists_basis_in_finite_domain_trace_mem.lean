-- Prove2me | solution 1 for GlobalTheory.exists_basis_in_finite_domain_trace_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:39:01.260206+00:00
-- url     : https://prove2.me/submissions/127ae33e-4886-4c64-9354-dc920d8c5482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (T C F K : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C]
    [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F K),
      (∀ (i : Fin n), ∃ (c : C), (algebraMap C K : C → K) c = (b : Fin n → K) i) ∧
        ∀ (i j : Fin n), ∃ (t : T), (algebraMap T F : T → F) t =
          (Algebra.trace F K : K → F) ((b : Fin n → K) i * (b : Fin n → K) j) := by
  classical
  have hint : ∀ c : C, IsIntegral T (algebraMap C K c) := fun c =>
    (Algebra.IsIntegral.isIntegral c).map (IsScalarTower.toAlgHom T C K)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  have hM0 : ∀ c : C,
      algebraMap C K c ∈ Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul t x _ hx =>
      have : algebraMap C K (t • x) = algebraMap T F t • algebraMap C K x := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T C K, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply T F K]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  let M0 : Submonoid K := MonoidHom.mrange (algebraMap C K).toMonoidHom
  have hA0 : Algebra.adjoin F (M0 : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective C z
    have ha : algebraMap C K a ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨a, rfl⟩)
    have hd' : algebraMap C K d ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨d, rfl⟩)
    have hinv : (algebraMap C K d)⁻¹ ∈ Algebra.adjoin F (M0 : Set K) :=
      Subalgebra.inv_mem_of_algebraic _ (x := ⟨_, hd'⟩) (hint d).tower_top.isAlgebraic
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ ha hinv
  have hspan : Submodule.span F (M0 : Set K) = ⊤ := by
    have h := Algebra.adjoin_eq_span F (M0 : Set K)
    rw [Submonoid.closure_eq, hA0, Algebra.top_toSubmodule] at h
    exact h.symm
  have htop : Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 fun x hx => by
      obtain ⟨c, rfl⟩ := MonoidHom.mem_mrange.1 hx
      exact hM0 c
  haveI : FiniteDimensional F K := ⟨⟨s.image (algebraMap C K), htop⟩⟩
  obtain ⟨B, hBsub, hBspan, hBli⟩ :=
    exists_linearIndependent F ((s.image (algebraMap C K) : Finset K) : Set K)
  have hBfin : B.Finite := (Finset.finite_toSet _).subset hBsub
  haveI := hBfin.fintype
  let b0 : Module.Basis B F K := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, htop])
  let b := b0.reindex (Fintype.equivFin B)
  have hbC : ∀ i, ∃ c : C, algebraMap C K c = b i := by
    intro i
    have hmem : b i ∈ B := by simp [b, b0]
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (hBsub hmem)
    exact ⟨c, hc⟩
  refine ⟨Fintype.card B, b, hbC, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := hbC i
  obtain ⟨c', hc'⟩ := hbC j
  have hI : IsIntegral T (b i * b j) := by
    rw [← hc, ← hc', ← map_mul]
    exact hint _
  exact IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace hI)
end _root_.GlobalTheory
end GlobalTheory
