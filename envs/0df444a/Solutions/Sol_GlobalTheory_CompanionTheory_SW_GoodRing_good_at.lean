-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.good_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:44.532112+00:00
-- url     : https://prove2.me/submissions/abc61758-5a24-40f5-8d36-02e8317652be

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_finite_maxSpec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_norm_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_fixed_unit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_eps
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_two
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_eq_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_subring
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_sigR_algebraMap
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_exists_integral_sq_sub_mul_sq_of_unit
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.GoodRing
theorem _root_.solution (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1) (hσ1 : σ (b₂ 1) = -b₂ 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (h31 : Valued.v (algebraMap F (Fv F v) 3) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F) :
    ∃ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F) ∧
      (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧
      (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧
      (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O,
        (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧
        ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧
      ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β →
        ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by
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
  obtain ⟨O, hOC, hOB⟩ := exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
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
  have hσB : sigR K σ (B 1) = -B 1 := by
    rw [hB1]
    show (1 : Fv F v) ⊗ₜ[F] σ (b₂ 1) = -((1 : Fv F v) ⊗ₜ[F] b₂ 1)
    rw [hσ1, TensorProduct.tmul_neg]
  have hstab : ∀ y ∈ O, sigR K σ y ∈ O := by
    intro y hy
    have hy' := (hOB y).1 hy
    rw [eq_coord B hB0 y, map_add, map_mul, sigR_algebraMap σ v, sigR_algebraMap σ v, hσB]
    have := hpq (B.repr y 0) (-(B.repr y 1)) (hy' 0) (Rs.neg_mem (hy' 1))
    simpa [map_neg] using this
  let τ : O →+* O := (sigR K σ).restrict O O hstab
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hτι : ∀ r, τ (ι r) = ι r := fun r => Subtype.ext (sigR_algebraMap σ v _)
  have hτδ : τ δ = -δ := Subtype.ext hσB
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
  have hv3 : Valued.v (3 : K) = 1 := by simpa [map_ofNat] using h31
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  have h3u : IsUnit (3 : v.adicCompletionIntegers F) := (hunit 3).2 (by
    rw [show ((3 : v.adicCompletionIntegers F) : K) = 3 from
      map_ofNat (v.adicCompletionIntegers F).subtype 3]
    exact hv3)
  refine ⟨O, hOC, hstab, finite_maxSpec ι δ hsp, ?_, ?_, ?_, ?_⟩
  · have := h2u.map ι
    rwa [map_ofNat] at this
  · refine ⟨δ, ?_, hσB⟩
    have h : IsUnit (δ * δ) := by rw [hδ]; exact hDu.map ι
    exact isUnit_of_mul_isUnit_left h
  · intro s β hβ hτβ
    obtain ⟨ε, z, h1, h2⟩ := exists_eps ι τ δ D' hδ hτι hτδ hsp hinj hDu h2u h3u s β hβ
      (Subtype.ext hτβ)
    exact ⟨ε, z, congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  · intro β hβ hτβ
    obtain ⟨c, hc, rfl⟩ := fixed_unit ι τ δ hτι hτδ hsp hinj h2u β hβ (Subtype.ext hτβ)
    obtain ⟨x, hx, y, hy, e⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v
      (algebraMap F K D) (c : K) hv2 hD1 ((hunit c).1 hc)
    refine ⟨ι ⟨x, hx⟩ + ι ⟨y, hy⟩ * δ, ?_⟩
    have h := norm_eq ι τ δ D' hδ hτι hτδ ⟨x, hx⟩ ⟨y, hy⟩
    have e' : (⟨x, hx⟩ : v.adicCompletionIntegers F) ^ 2 - D' * ⟨y, hy⟩ ^ 2 = c :=
      Subtype.ext e.symm
    rw [e'] at h
    exact congrArg Subtype.val h
end GlobalTheory.CompanionTheory.SW.GoodRing
