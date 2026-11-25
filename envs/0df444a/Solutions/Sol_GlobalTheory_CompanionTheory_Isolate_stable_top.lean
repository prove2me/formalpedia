-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Isolate.stable_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:40.190594+00:00
-- url     : https://prove2.me/submissions/cdc850ff-d2b6-49df-99b9-6ed75eb1871c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_exists_hk_avg
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
theorem _root_.solution {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F)))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V)
    (hi : π.IsIrreducible) (S : Submodule ℂ V) (hS : S ≤ fixed π K) (h0 : S ≠ ⊥)
    (hst : ∀ e, IsHk K e → ∀ s ∈ S, hk π K e s ∈ S) : fixed π K ≤ S := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hfin : ∀ L : Subgroup K, IsOpen (L : Set K) → Finite (K ⧸ L) := fun L hL =>
    Subgroup.quotient_finite_of_isOpen L hL
  let gen : Set V := {x | ∃ g, ∃ s ∈ S, x = π g s}
  let U : Subrepresentation π := ⟨Submodule.span ℂ gen, by
    intro g v hv
    have : Submodule.span ℂ gen ≤ (Submodule.span ℂ gen).comap (π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', s, hs, rfl⟩
      refine Submodule.subset_span ⟨g * g', s, hs, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    exact this hv⟩
  have hU : U = ⊤ := by
    rcases eq_bot_or_eq_top U with h | h
    · exfalso
      refine h0 ((Submodule.eq_bot_iff _).2 fun s hs => ?_)
      have h1 : s ∈ U.toSubmodule := Submodule.subset_span ⟨1, s, hs, by simp⟩
      rw [h] at h1
      exact (Submodule.mem_bot ℂ).1 h1
    · exact h
  have hall : ∀ w : V, w ∈ Submodule.span ℂ gen := by
    intro w
    have h1 : w ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← hU] at h1
    exact h1
  have hQ : ∀ w : V, ∃ L₀ : Subgroup K, IsOpen (L₀ : Set K) ∧ ∀ L : Subgroup K, IsOpen (L : Set K) → L ≤ L₀ →
      ∀ [Fintype (K ⧸ L)], ∑ q : K ⧸ L, π ((q.out : K) : GL ι F) w ∈ S := by
    intro w
    induction hall w using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, s, hs, rfl⟩ := hx
      let L₀ : Subgroup K := (K.comap (MulAut.conj g⁻¹).toMonoidHom).subgroupOf K
      refine ⟨L₀, ?_, ?_⟩
      · have hc : Continuous fun x : GL ι F => g⁻¹ * x * g := by fun_prop
        have := (hKo.preimage hc).preimage (continuous_subtype_val (p := (· ∈ K)))
        convert this using 1
        ext x
        simp [L₀, Subgroup.mem_subgroupOf]
      · intro L _ hLL _
        obtain ⟨e, he, h⟩ := exists_hk_avg hKo hKc L g (fun l hl => by
          have := hLL hl
          simpa [L₀, Subgroup.mem_subgroupOf] using this) π (hS hs)
        rw [← h]
        exact hst e he s hs
    | zero => exact ⟨⊤, by simp, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      obtain ⟨L₂, h₂, hy⟩ := hy
      refine ⟨L₁ ⊓ L₂, IsOpen.inter h₁ h₂, fun L hLo hL _ => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      exact S.add_mem (hx L hLo (hL.trans inf_le_left)) (hy L hLo (hL.trans inf_le_right))
    | smul c x _ hx =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      refine ⟨L₁, h₁, fun L hLo hL _ => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      exact S.smul_mem c (hx L hLo hL)
  intro w hw
  have hwk : ∀ k ∈ K, π k w = w := fun k hk' => by
    have := hw ⟨k, hk'⟩
    simpa using this
  obtain ⟨L, hLo, hL⟩ := hQ w
  haveI := hfin L hLo
  letI : Fintype (K ⧸ L) := Fintype.ofFinite _
  have h1 := hL L hLo le_rfl
  simp only [fun q : K ⧸ L => hwk _ (q.out : K).2, Finset.sum_const, Finset.card_univ] at h1
  have hn : ((Fintype.card (K ⧸ L) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  have h2 := S.smul_mem ((Fintype.card (K ⧸ L) : ℕ) : ℂ)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at h2
end GlobalTheory.CompanionTheory.Isolate
