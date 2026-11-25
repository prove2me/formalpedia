-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_next
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:48.628795+00:00
-- url     : https://prove2.me/submissions/6fca81b3-7a4b-48d3-9397-eb4d60007ce7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_hLin_apply
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_smul_right
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_add_right
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_smul_left
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_add_left
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_sum_left
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_conj
import Theorems.Thm_P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d
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
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution [Nontrivial A] (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hO : ∀ a ∈ O, c a ∈ O) {p q : A} (hp : p ∈ O) (hpc : c p = p) (hpq : p * q = 1)
    (hq : q ∉ O)
    (hloc : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) ∨ ∃ b ∈ O, a = p * b)
    (hθ : ∃ θ ∈ O, ∃ b ∈ O, (θ - c θ) * b = 1)
    (hnorm : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) → ∃ x ∈ O, c x * x = a)
    (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O)
    {k : ℕ} (hk : k < M) {e : Fin k → Fin M → A} (heL : ∀ i, e i ∈ L)
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    ∃ y ∈ L, (∀ i, hform c J (e i) y = 0) ∧ hform c J y y = 1 := by
  by_contra hcon
  let π : (Fin M → A) →ₗ[A] (Fin M → A) :=
    LinearMap.id - ∑ i, (hLin c J (e i)).smulRight (e i)
  have hπ : ∀ y, π y = y - ∑ i, hform c J (e i) y • e i := fun y => by
    simp [π, LinearMap.sum_apply, hLin_apply]
  have hπL : ∀ y ∈ L, π y ∈ L := fun y hy => by
    rw [hπ]
    exact sub_mem hy (sum_mem fun i _ => smul_mem' ((hL y).1 hy _ (heL i)) (heL i))
  have hπe : ∀ y j, hform c J (e j) (π y) = 0 := fun y j => by
    rw [hπ, ← hLin_apply, map_sub, map_sum]
    simp [hLin_apply, he]
  let N : Submodule O (Fin M → A) := L.map (π.restrictScalars O)
  have hN : ∀ y, y ∈ N ↔ y ∈ L ∧ ∀ j, hform c J (e j) y = 0 := fun y => by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hπL z hz, hπe z⟩
    · rintro ⟨hy, h⟩
      refine ⟨y, hy, ?_⟩
      show π y = y
      rw [hπ]; simp [h]
  have hqc : c q = q := by
    have := congrArg c hpq
    rw [map_mul, hpc, map_one] at this
    linear_combination q * this - c q * hpq

  have h1 : ∀ y ∈ N, q * hform c J y y ∈ O := by
    intro y hy
    obtain ⟨hyL, hy0⟩ := (hN y).1 hy
    have hfix := h_conj hc hJ y y
    rcases hloc _ ((hL y).1 hyL y hyL) hfix with ⟨b, hb, hb1⟩ | ⟨b, hb, hb1⟩
    · exfalso
      have hbc : c b = b := by
        have := congrArg c hb1
        rw [map_mul, hfix, map_one] at this
        linear_combination b * this - c b * hb1
      obtain ⟨a, ha, hab⟩ := hnorm b hb hbc ⟨_, (hL y).1 hyL y hyL, by rw [mul_comm, hb1]⟩
      refine hcon ⟨a • y, smul_mem' ha hyL, fun i => ?_, ?_⟩
      · rw [h_smul_right, hy0, mul_zero]
      · rw [h_smul_right, h_smul_left]
        linear_combination hform c J y y * hab + hb1
    · have : q * hform c J y y = b := by rw [hb1]; linear_combination b * hpq
      rwa [this]

  have h2 : ∀ y ∈ N, ∀ z ∈ N, q * hform c J z y ∈ O := by
    intro y hy z hz
    have htr : ∀ a ∈ O, q * (a * hform c J z y + c a * hform c J y z) ∈ O := by
      intro a ha
      have e1 := h1 _ (add_mem hz (smul_mem' ha hy))
      have e2 : q * (a * hform c J z y + c a * hform c J y z) =
          q * hform c J (z + a • y) (z + a • y) - q * hform c J z z -
            (c a * a) * (q * hform c J y y) := by
        simp only [h_add_left, h_add_right, h_smul_left, h_smul_right]
        ring
      rw [e2]
      exact sub_mem (sub_mem e1 (h1 z hz)) (mul_mem (mul_mem (hO a ha) ha) (h1 y hy))
    obtain ⟨θ, hθO, b, hb, hθb⟩ := hθ
    have e3 : q * hform c J z y = b * (q * (θ * hform c J z y + c θ * hform c J y z) -
        c θ * (q * (1 * hform c J z y + c 1 * hform c J y z))) := by
      rw [map_one]
      linear_combination (-(q * hform c J z y)) * hθb
    rw [e3]
    exact mul_mem hb (sub_mem (htr θ hθO) (mul_mem (hO θ hθO) (htr 1 (one_mem _))))
  have h3 : ∀ y ∈ N, q • y ∈ N := by
    intro y hy
    obtain ⟨hyL, hy0⟩ := (hN y).1 hy
    refine (hN _).2 ⟨(hL _).2 fun z hz => ?_, fun j => by rw [h_smul_right, hy0, mul_zero]⟩
    have e1 : z = π z + ∑ i, hform c J (e i) z • e i := by rw [hπ, sub_add_cancel]
    rw [h_smul_right, e1, h_add_left, h_sum_left]
    simp only [h_smul_left, hy0, mul_zero, Finset.sum_const_zero, add_zero]
    exact h2 y hy _ ⟨z, hz, rfl⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(⟨p, hp⟩ : O)}) N (hfg.map _) fun y hy => by
      have : y = (⟨p, hp⟩ : O) • (q • y) := by
        show y = p • (q • y)
        rw [smul_smul, hpq, one_smul]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (h3 y hy)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hr
  have ha' : (a : A) * p = r - 1 := congrArg Subtype.val ha
  have hca : c a * p = c r - 1 := by
    have := congrArg c ha'
    rwa [map_mul, hpc, map_sub, map_one] at this
  have hru : ∃ b, b * (r : A) = 1 := by
    rcases hloc (c r * r) (mul_mem (hO _ r.2) r.2) (by rw [map_mul, hc, mul_comm]) with
      ⟨b, -, hb⟩ | ⟨b, hb, hb1⟩
    · exact ⟨c r * b, by linear_combination hb⟩
    · exfalso
      apply hq
      have : q = b - c a * r - a := by
        linear_combination q * hb1 + q * r * hca + q * ha' + (b - c a * r - a) * hpq
      rw [this]
      exact sub_mem (sub_mem hb (mul_mem (hO _ a.2) r.2)) a.2
  obtain ⟨b, hb⟩ := hru
  have h4 : ∀ y, π y = 0 := by
    have : Submodule.span A (L : Set (Fin M → A)) ≤ LinearMap.ker π := by
      refine Submodule.span_le.2 fun y hy => ?_
      have h5 : (r : A) • π y = 0 := hr0 _ ⟨y, hy, rfl⟩
      show π y = 0
      rw [← one_smul A (π y), ← hb, mul_smul, h5, smul_zero]
    intro y
    exact this (hsp ▸ Submodule.mem_top)
  have h6 : Submodule.span A (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have := h4 y
    rw [hπ, sub_eq_zero] at this
    rw [this]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h7 := finrank_le_of_span_eq_top h6
  simp at h7
  omega
end GlobalTheory.UnramSelfDual
