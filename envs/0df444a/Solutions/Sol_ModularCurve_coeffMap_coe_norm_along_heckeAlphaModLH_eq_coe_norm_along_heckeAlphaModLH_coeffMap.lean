-- Prove2me | solution 1 for ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/56b25b05-b287-5e1d-8aad-1d28703d184a

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap

set_option autoImplicit false

open ModularCurve AlgebraicCurve
open scoped MatrixGroups

namespace KappaNorm

open Module

theorem map_norm_eq_norm_map {F E F' E' : Type*} [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E'] [Module.Finite F E] [Module.Finite F' E']
    (φ : F →+* F') (ψ : E →+* E')
    (hcomm : ∀ c : F, ψ (algebraMap F E c) = algebraMap F' E' (φ c))
    (hgen : ∀ S : Subalgebra F' E', Set.range ψ ⊆ S → S = ⊤)
    (hdeg : finrank F E = finrank F' E') (x : E) :
    φ (Algebra.norm F x) = Algebra.norm F' (ψ x) := by
  classical

  set n := finrank F E with hn
  let b : Basis (Fin n) F E := Module.finBasisOfFinrankEq F E rfl

  let b' : Fin n → E' := fun i => ψ (b i)
  have hsmul : ∀ (c : F) (e : E), ψ (c • e) = φ c • ψ e := by
    intro c e
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomm]
  have hψsum : ∀ e : E, ψ e = ∑ i, φ (b.repr e i) • b' i := by
    intro e
    conv_lhs => rw [← b.sum_repr e]
    rw [map_sum]
    simp only [hsmul, b']
  let S : Subalgebra F' E' :=
    { carrier := Submodule.span F' (Set.range b')
      mul_mem' := by
        intro u v hu hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
        · rintro _ ⟨i, rfl⟩
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · rintro _ ⟨k, rfl⟩
            show ψ (b i) * ψ (b k) ∈ Submodule.span F' (Set.range b')
            rw [← map_mul, hψsum]
            exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
          · rw [mul_zero]; exact Submodule.zero_mem _
          · intro a c _ _ ha hc; rw [mul_add]; exact Submodule.add_mem _ ha hc
          · intro r a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
        · rw [zero_mul]; exact Submodule.zero_mem _
        · intro a c _ _ ha hc; rw [add_mul]; exact Submodule.add_mem _ ha hc
        · intro r a _ ha; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha
      one_mem' := by
        show (1 : E') ∈ Submodule.span F' (Set.range b')
        rw [← map_one ψ, hψsum]
        exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := by
        intro c
        show algebraMap F' E' c ∈ Submodule.span F' (Set.range b')
        rw [Algebra.algebraMap_eq_smul_one]
        refine Submodule.smul_mem _ _ ?_
        show (1 : E') ∈ Submodule.span F' (Set.range b')
        rw [← map_one ψ, hψsum]
        exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩) }
  have hS : S = ⊤ := hgen S (by
    rintro _ ⟨e, rfl⟩
    show ψ e ∈ Submodule.span F' (Set.range b')
    rw [hψsum]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  have hspan : ⊤ ≤ Submodule.span F' (Set.range b') := by
    intro e _
    have : e ∈ S := by rw [hS]; exact Algebra.mem_top
    exact this
  have hcard : Fintype.card (Fin n) = finrank F' E' := by rw [Fintype.card_fin]; exact hdeg
  let B : Basis (Fin n) F' E' := basisOfTopLeSpanOfCardEqFinrank b' hspan hcard
  have hB : ∀ i, B i = ψ (b i) := fun i => by
    simp only [B, coe_basisOfTopLeSpanOfCardEqFinrank, b']

  have hmat : Algebra.leftMulMatrix B (ψ x) = (Algebra.leftMulMatrix b x).map φ := by
    ext i k
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hB]
    have h1 : ψ x * ψ (b k) = ∑ m, φ (b.repr (x * b k) m) • B m := by
      rw [← map_mul, hψsum]; simp only [hB, b']
    rw [h1, map_sum]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finset.sum_apply']
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.single_eq_same]
    · intro m _ hm; rw [Finsupp.single_apply, if_neg hm]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det b, hmat, RingHom.map_det]
  rfl

end KappaNorm

namespace KappaNorm
open ModularCurve

noncomputable def resMap {k K : Type*} [Field k] [Field K] (j : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) where
  toFun y := ⟨coeffMap j (y : LaurentSeries k), coeffMap_mem_qExpFunctionFieldC_of_mem j Γ y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_resMap {k K : Type*} [Field k] [Field K] (j : k →+* K) (Γ : Subgroup SL(2, ℤ)) (y : ↥(qExpFunctionFieldC k Γ)) :
    ((resMap j Γ y : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap j (y : LaurentSeries k) := rfl

end KappaNorm
p2m_reactivate "P2MW.S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap.KappaNorm"

theorem solution
    (k K : Type*) [Field k] [Field K] (j : k →+* K)
    (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hfink : FiniteAlong k (heckeAlphaModLH k N H ℓ)) (hfinK : FiniteAlong K (heckeAlphaModLH K N H ℓ))
    (hdeg : finrankAlong k (heckeAlphaModLH k N H ℓ) = finrankAlong K (heckeAlphaModLH K N H ℓ))
    (x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) :
    coeffMap j (((letI := algebraAlong (heckeAlphaModLH k N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) x) : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H))) : LaurentSeries k) =
      (((letI := algebraAlong (heckeAlphaModLH K N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))
          (⟨coeffMap j (x : LaurentSeries k),
            coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) x.2⟩ :
            ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))) :
          ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))) : LaurentSeries K) := by
  classical
  letI instk : Algebra ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) := algebraAlong (heckeAlphaModLH k N H ℓ)
  letI instK : Algebra ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) := algebraAlong (heckeAlphaModLH K N H ℓ)
  haveI hfk : @Module.Finite ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) _ _ (Algebra.toModule) := hfink
  haveI hfK : @Module.Finite ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) _ _ (Algebra.toModule) := hfinK
  have hdeg' : @Module.finrank ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) _ _ (Algebra.toModule) = @Module.finrank ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) _ _ (Algebra.toModule) := hdeg

  let φ := KappaNorm.resMap j (CohCarrier.GammaH N H)
  let ψ := KappaNorm.resMap j (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))
  have hcomm : ∀ c : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)), ψ (algebraMap ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) c) = algebraMap ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) (φ c) := by
    intro c
    apply Subtype.ext
    show coeffMap j ((heckeAlphaModLH k N H ℓ c : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) : LaurentSeries k) = ((heckeAlphaModLH K N H ℓ (φ c) : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) : LaurentSeries K)
    rw [coe_heckeAlphaModLH, coe_heckeAlphaModLH, KappaNorm.coe_resMap]

  have hgen : ∀ S : Subalgebra ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))), Set.range ψ ⊆ S → S = ⊤ := by
    intro S hS
    haveI : Algebra.IsAlgebraic ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) := Algebra.IsAlgebraic.of_finite _ _
    have hSfield : IsField S := Subalgebra.isField_of_algebraic S
    apply eq_top_iff.mpr
    rintro ⟨z, hz⟩ -
    have hEq := (ModularCurve.coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap k K j
      (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))).2
    have toK : ∀ {w : LaurentSeries K}, w ∈ IntermediateField.adjoin K (coeffMap j '' (qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) : Set (LaurentSeries k))) →
        w ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) := by
      intro w hw; rw [hEq]; exact hw
    have hz' : z ∈ IntermediateField.adjoin K (coeffMap j '' (qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) : Set (LaurentSeries k))) := by
      rw [← hEq]; exact hz
    suffices H : ∀ hz'' : z ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)), (⟨z, hz''⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) ∈ S from H hz
    clear hz
    induction hz' using IntermediateField.adjoin_induction with
    | mem y hy =>
        intro hyK
        obtain ⟨w, hw, rfl⟩ := hy
        have : (⟨coeffMap j w, hyK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = ψ ⟨w, hw⟩ := rfl
        rw [this]
        exact hS ⟨_, rfl⟩
    | algebraMap c =>
        intro hcK
        have : (⟨algebraMap K (LaurentSeries K) c, hcK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = algebraMap ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) (algebraMap K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) c) := by
          apply Subtype.ext
          show algebraMap K (LaurentSeries K) c = ((heckeAlphaModLH K N H ℓ (algebraMap K _ c) : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) : LaurentSeries K)
          rw [AlgHom.commutes]; rfl
        rw [this]
        exact S.algebraMap_mem _
    | add x y hx hy ihx ihy =>
        intro hK
        have e : (⟨x + y, hK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = ⟨x, toK hx⟩ + ⟨y, toK hy⟩ := rfl
        rw [e]; exact S.add_mem (ihx (toK hx)) (ihy (toK hy))
    | inv x hx ih =>
        intro hK
        have hxK := toK hx
        have e : (⟨x⁻¹, hK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = ⟨x, hxK⟩⁻¹ := rfl
        rw [e]
        by_cases h0 : (⟨x, hxK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = 0
        · rw [h0, inv_zero]; exact S.zero_mem
        · obtain ⟨y, hy1⟩ := hSfield.mul_inv_cancel (a := ⟨⟨x, hxK⟩, ih hxK⟩) (fun h => h0 (congrArg Subtype.val h))
          have hy2 : (⟨x, hxK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) * (y : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = 1 := congrArg Subtype.val hy1
          have : (⟨x, hxK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))⁻¹ = y := by
            rw [inv_eq_of_mul_eq_one_right hy2]
          rw [this]; exact y.2
    | mul x y hx hy ihx ihy =>
        intro hK
        have e : (⟨x * y, hK⟩ : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) = ⟨x, toK hx⟩ * ⟨y, toK hy⟩ := rfl
        rw [e]; exact S.mul_mem (ihx (toK hx)) (ihy (toK hy))
  have main := @KappaNorm.map_norm_eq_norm_map ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) _ _ _ _ instk instK hfk hfK φ ψ hcomm hgen hdeg' x
  have := congrArg (fun w : ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H)) => (w : LaurentSeries K)) main
  exact this.symm.symm

#print axioms solution

end S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
end P2MW
export P2MW.S_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap (solution)
