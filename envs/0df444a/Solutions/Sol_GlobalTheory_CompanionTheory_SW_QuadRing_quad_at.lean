-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadRing.quad_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:06:14.225633+00:00
-- url     : https://prove2.me/submissions/9a5c292f-5488-4881-9608-806ec3a6ad44

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_two
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_eq_coord
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadRing
open GlobalTheory.CompanionTheory.SW.GoodRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.QuadRing
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F),
      (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧
      (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧
      IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  have hBC' : ∀ k j, B.repr (C k) j ∈ Rs := fun k j => by
    have := hBC k j
    rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hCB' : ∀ j k, C.repr (B j) k ∈ Rs := fun j k => by
    have := hCB j k
    rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    ⟨fun hy j => coord_mem Rs C B hBC' y ((hO y).1 hy) j,
      fun hy => (hO y).2 fun k => coord_mem Rs B C hCB' y hy k⟩
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hinj : ∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' : algebraMap K (K ⊗[F] E) (p : K) + algebraMap K (K ⊗[F] E) (q : K) * B 1 = 0 :=
      congrArg Subtype.val h
    have hc := coord_two B hB0 (p : K) (q : K)
    rw [h'] at hc
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    exact ⟨Subtype.ext hc.1.symm, Subtype.ext hc.2.symm⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  exact ⟨ι, δ, D', hδ, hsp, hinj, hDu, h2u⟩
end GlobalTheory.CompanionTheory.SW.QuadRing
