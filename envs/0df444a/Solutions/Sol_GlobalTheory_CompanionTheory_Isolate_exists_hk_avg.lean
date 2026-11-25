-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Isolate.exists_hk_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:41.095537+00:00
-- url     : https://prove2.me/submissions/3aee4ea9-3407-4aa7-8449-edd2bd73d8ea

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_unitFn_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_unitFn_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
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
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Isolate
open GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Isolate
theorem _root_.solution {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) (L : Subgroup K) [Fintype (K ⧸ L)] (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * ((l : K) : GL ι F) * g ∈ K)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {s : V}
    (hs : s ∈ fixed ρ K) :
    ∃ e, IsHk K e ∧ hk ρ K e s = ∑ q : K ⧸ L, ρ ((q.out : K) : GL ι F) (ρ g s) := by
  classical
  have hsk : ∀ k ∈ K, ρ k s = s := fun k hk' => by
    have := hs ⟨k, hk'⟩
    simpa using this
  let a : K ⧸ L → GL ι F := fun q => ((q.out : K) : GL ι F) * g
  have key : ∀ (k : K) (q : K ⧸ L), ∃ c ∈ K, (k : GL ι F) * a q = a (k • q) * c := by
    intro k q
    have hq : ((k * q.out : K) : K ⧸ L) = k • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hmem : ((k • q).out)⁻¹ * (k * q.out) ∈ L := by
      apply QuotientGroup.eq.1
      rw [hq, QuotientGroup.out_eq']
    refine ⟨_, hL _ hmem, ?_⟩
    simp only [a]
    push_cast
    group
  let e : GL ι F → ℂ := fun x => ∑ q, unitFn K ((a q)⁻¹ * x)
  have hright : ∀ x, ∀ k ∈ K, e (x * k) = e x := fun x k hk' =>
    Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, unitFn_mul_right _ hk']
  have hleft : ∀ x, ∀ k ∈ K, e (k * x) = e x := by
    intro x k hk'
    let k' : K := ⟨k⁻¹, K.inv_mem hk'⟩
    have h1 : ∀ q, unitFn K ((a q)⁻¹ * (k * x)) = unitFn K ((a (k' • q))⁻¹ * x) := by
      intro q
      obtain ⟨c, hc, h⟩ := key k' q
      have h2 : (a q)⁻¹ * (k * x) = c⁻¹ * ((a (k' • q))⁻¹ * x) := by
        have h3 : (a q)⁻¹ * k = c⁻¹ * (a (k' • q))⁻¹ := by
          rw [← mul_inv_rev, ← h]
          simp [k']
        rw [← mul_assoc, h3, mul_assoc]
      rw [h2, unitFn_mul_left _ (K.inv_mem hc)]
    simp only [e, h1]
    exact Fintype.sum_equiv (MulAction.toPerm k') _ _ (fun _ => rfl)
  have hsupp : ∀ x, e x ≠ 0 → ∃ q, (a q)⁻¹ * x ∈ K := by
    intro x hx
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    refine ⟨q, ?_⟩
    by_contra h
    exact hq (by simp [unitFn, h])
  have hE : IsHk K e := by
    refine ⟨hKo, hKc, ?_, ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact
        (K := ⋃ q, (fun y => a q * y) '' (K : Set (GL ι F)))
        (isCompact_iUnion fun q => hKc.image (continuous_mul_left _)) ?_
      intro x hx
      obtain ⟨q, hq⟩ := hsupp x hx
      exact Set.mem_iUnion.2 ⟨q, _, hq, by simp⟩
    · intro k₁ hk₁ k₂ hk₂ x
      rw [hright _ _ hk₂, hleft _ _ hk₁]
  refine ⟨e, hE, ?_⟩
  let B : Finset (GL ι F ⧸ K) := Finset.univ.image fun q => (QuotientGroup.mk (a q) : GL ι F ⧸ K)
  have hB : ∀ p : GL ι F ⧸ K, e p.out ≠ 0 → p ∈ B := by
    intro p hp
    obtain ⟨q, hq⟩ := hsupp _ hp
    refine Finset.mem_image.2 ⟨q, Finset.mem_univ _, ?_⟩
    rw [← QuotientGroup.out_eq' p]
    exact QuotientGroup.eq.2 hq
  rw [hk_eq_sum ρ K e s B hB]
  simp only [e, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single (QuotientGroup.mk (a q))]
  · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (a q)
    have h1 : unitFn K ((a q)⁻¹ * (a q * (c : GL ι F))) = 1 := by
      rw [inv_mul_cancel_left]
      simp [unitFn]
    rw [hc, h1, one_smul, map_mul, Module.End.mul_apply, hsk _ c.2, map_mul, Module.End.mul_apply]
  · intro p _ hp
    have h1 : unitFn K ((a q)⁻¹ * p.out) = 0 := by
      unfold unitFn
      rw [if_neg]
      intro h
      refine hp ?_
      rw [← QuotientGroup.out_eq' p]
      exact (QuotientGroup.eq.2 h).symm
    rw [h1, zero_smul]
  · intro h
    exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ q)) h
end GlobalTheory.CompanionTheory.Isolate
