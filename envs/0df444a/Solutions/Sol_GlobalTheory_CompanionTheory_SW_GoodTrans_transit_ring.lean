-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodTrans.transit_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:14.798557+00:00
-- url     : https://prove2.me/submissions/8ca415a1-265b-47b2-90f1-343a9b6490f1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuasiRefl_exists_unitary_carry
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodTrans
namespace GlobalTheory.CompanionTheory.SW.GoodTrans
theorem _root_.solution {T : Type} [CommRing T] (O : Subring T) (s : T →+* T)
    (hs : ∀ y ∈ O, s y ∈ O) (hss : ∀ y, s (s y) = y) {M : ℕ} (JT : Matrix (Fin M) (Fin M) T)
    (hJO : ∀ i j, JT i j ∈ O) (hJ : ∀ i j, s (JT j i) = JT i j) (x y : Fin M → T)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (hxy : hform s JT x x = hform s JT y y)
    (w : T) (hw : w ∈ O) (hxw : hform s JT x x * w = 1)
    (hgood : ∀ p β : O, IsUnit β → s β = β → ∃ ε z : O,
      (ε : T) * s ε = 1 ∧ ((β : T) - s ε * p) * z = 1) :
    ∃ g ∈ UJ s JT, (g : Matrix (Fin M) (Fin M) T) *ᵥ x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) T) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) i j ∈ O := by
  let τ : O →+* O := s.restrict O O hs
  have hτ : ∀ a : O, ((τ a : O) : T) = s a := fun a => rfl
  let JO : Matrix (Fin M) (Fin M) O := fun i j => ⟨JT i j, hJO i j⟩
  let x0 : Fin M → O := fun i => ⟨x i, hx i⟩
  let y0 : Fin M → O := fun i => ⟨y i, hy i⟩
  have hcoe : ∀ p q : Fin M → O, ((hform τ JO p q : O) : T) =
      hform s JT (fun i => (p i : T)) (fun i => (q i : T)) := by
    intro p q
    simp [hform, hτ, JO]
  have hβ0 : ((hform τ JO x0 x0 : O) : T) = hform s JT x x := hcoe x0 x0
  have hxy0 : hform τ JO x0 x0 = hform τ JO y0 y0 := Subtype.ext (by
    rw [hβ0, hxy]; exact (hcoe y0 y0).symm)
  have hunit : IsUnit (hform τ JO x0 x0) :=
    IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext (by
      rw [Subring.coe_mul, hβ0]; exact hxw))
  have hτinv : ∀ a : O, τ (τ a) = a := fun a => Subtype.ext (hss a)
  have hJ0 : ∀ i j, τ (JO j i) = JO i j := fun i j => Subtype.ext (hJ i j)
  have hfix : s (hform τ JO x0 x0 : O) = (hform τ JO x0 x0 : O) := by
    have := GlobalTheory.CompanionTheory.SW.QuasiRefl.hform_conj_symm hτinv hJ0 x0 x0
    exact congrArg Subtype.val this
  obtain ⟨ε, z, hε, hz⟩ := hgood (hform τ JO y0 x0) _ hunit hfix
  have hε' : ε * τ ε = 1 := Subtype.ext hε
  have hu : IsUnit (hform τ JO x0 x0 - τ ε * hform τ JO y0 x0) :=
    IsUnit.of_mul_eq_one z (Subtype.ext hz)
  obtain ⟨g0, hg0, hgx, -⟩ := GlobalTheory.CompanionTheory.SW.QuasiRefl.exists_unitary_carry O τ hτinv M JO hJ0 x0 y0 ε
    hxy0 hunit hε' hu
  have hval : ∀ g : GL (Fin M) O, ((bc O.subtype g : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) =
      (g : Matrix (Fin M) (Fin M) O).map O.subtype := fun g => rfl
  refine ⟨bc O.subtype g0, ?_, ?_, ?_, ?_⟩
  · have h0 : cT τ (g0 : Matrix (Fin M) (Fin M) O) * JO * (g0 : Matrix (Fin M) (Fin M) O) = JO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) * JT *
      ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) = JT
    have e1 : RingHom.mapMatrix O.subtype (cT τ (g0 : Matrix (Fin M) (Fin M) O)) =
        cT s ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := by
      ext i j
      rfl
    have e2 : RingHom.mapMatrix O.subtype JO = JT := by
      ext i j
      rfl
    have e3 : RingHom.mapMatrix O.subtype (g0 : Matrix (Fin M) (Fin M) O) =
        ((bc O.subtype g0 : GL (Fin M) T) : Matrix (Fin M) (Fin M) T) := rfl
    rwa [e1, e2, e3] at h1
  · funext i
    have := congrArg Subtype.val (congrFun hgx i)
    simpa [Matrix.mulVec, dotProduct, hval, x0, y0] using this
  · intro i j
    rw [hval]
    exact ((g0 : Matrix (Fin M) (Fin M) O) i j).2
  · intro i j
    rw [← map_inv, hval]
    exact (((g0⁻¹ : GL (Fin M) O) : Matrix (Fin M) (Fin M) O) i j).2
end GlobalTheory.CompanionTheory.SW.GoodTrans
