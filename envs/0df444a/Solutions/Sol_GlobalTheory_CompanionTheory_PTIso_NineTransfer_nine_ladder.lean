-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.NineTransfer.nine_ladder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:47.74683+00:00
-- url     : https://prove2.me/submissions/12449ffa-3e23-44b5-897b-b91c16b5e1aa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_exact_transfer
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
theorem _root_.solution {X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 X0' X1' X2' Y0' Y1' Y2' W0' W1' W2' : Type*}
    [AddCommGroup X0] [Module R X0] [AddCommGroup X1] [Module R X1]
    [AddCommGroup X2] [Module R X2] [AddCommGroup Y0] [Module R Y0]
    [AddCommGroup Y1] [Module R Y1] [AddCommGroup Y2] [Module R Y2]
    [AddCommGroup W0] [Module R W0] [AddCommGroup W1] [Module R W1]
    [AddCommGroup W2] [Module R W2]
    [AddCommGroup X0'] [Module R X0'] [AddCommGroup X1'] [Module R X1']
    [AddCommGroup X2'] [Module R X2'] [AddCommGroup Y0'] [Module R Y0']
    [AddCommGroup Y1'] [Module R Y1'] [AddCommGroup Y2'] [Module R Y2']
    [AddCommGroup W0'] [Module R W0'] [AddCommGroup W1'] [Module R W1']
    [AddCommGroup W2'] [Module R W2']
    (a0 : X0' ≃ₗ[R] X0) (a1 : X1' ≃ₗ[R] X1) (a2 : X2' ≃ₗ[R] X2)
    (p0 : Y0' ≃ₗ[R] Y0) (p1 : Y1' ≃ₗ[R] Y1) (p2 : Y2' ≃ₗ[R] Y2)
    (w0 : W0' ≃ₗ[R] W0) (w1 : W1' ≃ₗ[R] W1) (w2 : W2' ≃ₗ[R] W2)
    {g0 : X0 →ₗ[R] Y0} {g1 : X1 →ₗ[R] Y1} {g2 : X2 →ₗ[R] Y2}
    {t0 : Y0 →ₗ[R] W0} {t1 : Y1 →ₗ[R] W1} {t2 : Y2 →ₗ[R] W2}
    {g0' : X0' →ₗ[R] Y0'} {g1' : X1' →ₗ[R] Y1'} {g2' : X2' →ₗ[R] Y2'}
    {t0' : Y0' →ₗ[R] W0'} {t1' : Y1' →ₗ[R] W1'} {t2' : Y2' →ₗ[R] W2'}
    (hg0 : ∀ x, g0 (a0 x) = p0 (g0' x)) (hg1 : ∀ x, g1 (a1 x) = p1 (g1' x))
    (hg2 : ∀ x, g2 (a2 x) = p2 (g2' x))
    (ht0 : ∀ y, t0 (p0 y) = w0 (t0' y)) (ht1 : ∀ y, t1 (p1 y) = w1 (t1' y))
    (ht2 : ∀ y, t2 (p2 y) = w2 (t2' y))
    (h : ∃ (d1' : W0' →ₗ[R] X1') (d2' : W1' →ₗ[R] X2'),
      Function.Injective g0' ∧ Function.Exact g0' t0' ∧ Function.Exact t0' d1' ∧
      Function.Exact d1' g1' ∧ Function.Exact g1' t1' ∧ Function.Exact t1' d2' ∧
      Function.Exact d2' g2' ∧ Function.Exact g2' t2' ∧ Function.Surjective t2') :
    ∃ (d1 : W0 →ₗ[R] X1) (d2 : W1 →ₗ[R] X2),
      Function.Injective g0 ∧ Function.Exact g0 t0 ∧ Function.Exact t0 d1 ∧
      Function.Exact d1 g1 ∧ Function.Exact g1 t1 ∧ Function.Exact t1 d2 ∧
      Function.Exact d2 g2 ∧ Function.Exact g2 t2 ∧ Function.Surjective t2 := by
  obtain ⟨d1', d2', i0, e1, e2, e3, e4, e5, e6, e7, s8⟩ := h
  have hd1 : ∀ y, (a1.toLinearMap ∘ₗ d1' ∘ₗ w0.symm.toLinearMap) (w0 y) = a1 (d1' y) := by
    intro y; simp
  have hd2 : ∀ y, (a2.toLinearMap ∘ₗ d2' ∘ₗ w1.symm.toLinearMap) (w1 y) = a2 (d2' y) := by
    intro y; simp
  refine ⟨a1.toLinearMap ∘ₗ d1' ∘ₗ w0.symm.toLinearMap,
    a2.toLinearMap ∘ₗ d2' ∘ₗ w1.symm.toLinearMap, ?_, exact_transfer a0 p0 w0 hg0 ht0 e1,
    exact_transfer p0 w0 a1 ht0 hd1 e2, exact_transfer w0 a1 p1 hd1 hg1 e3,
    exact_transfer a1 p1 w1 hg1 ht1 e4, exact_transfer p1 w1 a2 ht1 hd2 e5,
    exact_transfer w1 a2 p2 hd2 hg2 e6, exact_transfer a2 p2 w2 hg2 ht2 e7, ?_⟩
  · intro x y hxy
    obtain ⟨x', rfl⟩ := a0.surjective x
    obtain ⟨y', rfl⟩ := a0.surjective y
    rw [hg0, hg0] at hxy
    rw [i0 (p0.injective hxy)]
  · intro w
    obtain ⟨y', hy⟩ := s8 (w2.symm w)
    exact ⟨p2 y', by rw [ht2, hy]; simp⟩
end GlobalTheory.CompanionTheory.PTIso.NineTransfer
