-- Prove2me | solution 1 for ModularCurve.map_differentialCorrespondence_eq_heckeDiffBar_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bf2ad2de-afde-5857-be7a-d2d595274844

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map

set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential AlgebraicCurve

namespace DiffBC

noncomputable def kappa (K E : Type*) {F FE : Type*} [Field K] [Field E] [Field F] [Field FE]
    [Algebra K E] [Algebra K F] [Algebra E FE] [Algebra K FE] [IsScalarTower K E FE]
    (ι : F →ₐ[K] FE) : Ω[F⁄K] →ₗ[K] Ω[FE⁄E] :=
  (KaehlerDifferential.map K E FE FE).restrictScalars K ∘ₗ Differential.pullbackAlong ι

theorem kappa_apply (K E : Type*) {F FE : Type*} [Field K] [Field E] [Field F] [Field FE]
    [Algebra K E] [Algebra K F] [Algebra E FE] [Algebra K FE] [IsScalarTower K E FE]
    (ι : F →ₐ[K] FE) (ω : Ω[F⁄K]) :
    kappa K E ι ω = KaehlerDifferential.map K E FE FE (Differential.pullbackAlong ι ω) := rfl

theorem kappa_smul (K E : Type*) {F FE : Type*} [Field K] [Field E] [Field F] [Field FE]
    [Algebra K E] [Algebra K F] [Algebra E FE] [Algebra K FE] [IsScalarTower K E FE]
    (ι : F →ₐ[K] FE) (f : F) (ω : Ω[F⁄K]) :
    kappa K E ι (f • ω) = ι f • kappa K E ι ω := by
  rw [kappa_apply, kappa_apply, Differential.pullbackAlong_smul, LinearMap.map_smul]

section Span

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem induction_on_smul_pullbackAlong (φ : F →ₐ[K] F') (hφ : SeparableAlong K φ)
    {P : Ω[F'⁄K] → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (u : F') (ω : Ω[F⁄K]), P (u • Differential.pullbackAlong φ ω)) (x : Ω[F'⁄K]) : P x := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Algebra.IsSeparable F F' := hφ
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective x
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact h0
  | tmul u ω =>
    have e : KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω) =
        u • Differential.pullbackAlong φ ω := by
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [e]; exact hsmul u ω
  | add s t hs ht => rw [map_add]; exact hadd _ _ hs ht

end Span

section Trace

variable {K E F F' FE F'E : Type*} [Field K] [Field E] [Field F] [Field F'] [Field FE]
    [Field F'E] [Algebra K E] [Algebra K F] [Algebra K F'] [Algebra E FE] [Algebra E F'E] [Algebra K FE]
    [Algebra K F'E] [IsScalarTower K E FE] [IsScalarTower K E F'E]

omit [Algebra K E] [IsScalarTower K E FE] [IsScalarTower K E F'E] in

theorem trace_along_eq (ι : F →ₐ[K] FE) (ι' : F' →ₐ[K] F'E) (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hcomm : ∀ f, φE (ι f) = ι' (φ f))
    {n : Type*} [Fintype n] [DecidableEq n] (b : n → F')
    (hb : letI := algebraAlong φ; LinearIndependent F b ∧ Submodule.span F (Set.range b) = ⊤)
    (hb' : letI := algebraAlong φE;
      LinearIndependent FE (fun i => ι' (b i)) ∧ Submodule.span FE (Set.range fun i => ι' (b i)) = ⊤)
    (u : F') :
    (letI := algebraAlong φE; Algebra.trace FE F'E (ι' u)) = ι (letI := algebraAlong φ; Algebra.trace F F' u) := by
  letI iF := algebraAlong φ
  letI iE := algebraAlong φE
  let B : Module.Basis n F F' := Module.Basis.mk hb.1 hb.2.ge
  let B' : Module.Basis n FE F'E := Module.Basis.mk hb'.1 hb'.2.ge
  have hB : ∀ i, B i = b i := fun i => Module.Basis.mk_apply hb.1 hb.2.ge i
  have hB' : ∀ i, B' i = ι' (b i) := fun i => Module.Basis.mk_apply hb'.1 hb'.2.ge i

  have key : ∀ i j, B'.repr (ι' u * B' j) i = ι (B.repr (u * B j) i) := by
    intro i j
    have hsum : u * B j = ∑ k, (B.repr (u * B j) k) • B k := (B.sum_repr (u * B j)).symm
    have hsum' : ι' u * B' j = ∑ k, (ι (B.repr (u * B j) k)) • B' k := by
      have h1 := congrArg ι' hsum
      rw [map_mul ι', map_sum ι'] at h1
      rw [hB' j, ← hB j, h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hB k, hB' k, Algebra.smul_def, Algebra.smul_def, map_mul ι']
      congr 1
      exact (hcomm _).symm
    rw [hsum', map_sum]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finset.sum_apply', Finsupp.single_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => if_neg hk) (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  rw [Algebra.trace_eq_matrix_trace B u, Algebra.trace_eq_matrix_trace B' (ι' u), Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  exact key i i

theorem kappa_traceAlong (ι : F →ₐ[K] FE) (ι' : F' →ₐ[K] F'E) (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hcomm : ∀ f, φE (ι f) = ι' (φ f))
    (hφ : SeparableAlong K φ) (hφE : SeparableAlong E φE)
    {n : Type*} [Fintype n] [DecidableEq n] (b : n → F')
    (hb : letI := algebraAlong φ; LinearIndependent F b ∧ Submodule.span F (Set.range b) = ⊤)
    (hb' : letI := algebraAlong φE;
      LinearIndependent FE (fun i => ι' (b i)) ∧ Submodule.span FE (Set.range fun i => ι' (b i)) = ⊤)
    (hpull : ∀ ω : Ω[F⁄K], kappa K E ι' (Differential.pullbackAlong φ ω) =
      Differential.pullbackAlong φE (kappa K E ι ω))
    (u : Ω[F'⁄K]) :
    kappa K E ι (Differential.traceAlong φ u) =
      Differential.traceAlong φE (kappa K E ι' u) := by
  induction u using induction_on_smul_pullbackAlong φ hφ with
  | h0 => rw [map_zero, map_zero, map_zero, map_zero]
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | hsmul u ω =>
    rw [Differential.traceAlong_smul_pullbackAlong φ hφ u ω, kappa_smul, kappa_smul, hpull,
      Differential.traceAlong_smul_pullbackAlong φE hφE (ι' u) (kappa K E ι ω),
      trace_along_eq ι ι' φ φE hcomm b hb hb' u]

end Trace

end DiffBC

namespace DiffBC

section

variable {K E F FE : Type*} [Field K] [Field E] [Field F] [Field FE]
    [Algebra K E] [Algebra K F] [Algebra E FE] [Algebra K FE] [IsScalarTower K E FE]

theorem kappa_D (ι : F →ₐ[K] FE) (g : F) :
    kappa K E ι (D K F g) = D E FE (ι g) := by
  rw [kappa_apply, Differential.pullbackAlong_D, KaehlerDifferential.map_D]
  rfl

theorem kappa_smul_D (ι : F →ₐ[K] FE) (f g : F) :
    kappa K E ι (f • D K F g) = ι f • D E FE (ι g) := by
  rw [kappa_smul, kappa_D]

end

theorem kappa_pullbackAlong {K E F F' FE F'E : Type*} [Field K] [Field E] [Field F] [Field F'] [Field FE]
    [Field F'E] [Algebra K E] [Algebra K F] [Algebra K F'] [Algebra E FE] [Algebra E F'E] [Algebra K FE]
    [Algebra K F'E] [IsScalarTower K E FE] [IsScalarTower K E F'E]
    (ι : F →ₐ[K] FE) (ι' : F' →ₐ[K] F'E) (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hcomm : ∀ f, φE (ι f) = ι' (φ f)) (ω : Ω[F⁄K]) :
    kappa K E ι' (Differential.pullbackAlong φ ω) = Differential.pullbackAlong φE (kappa K E ι ω) := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [Differential.pullbackAlong_D, kappa_D, kappa_D, Differential.pullbackAlong_D, hcomm]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [Differential.pullbackAlong_smul, kappa_smul, hx, kappa_smul, Differential.pullbackAlong_smul, hcomm]

end DiffBC

namespace DiffBC

section BasisTransport

variable {K E F F' FE F'E : Type*} [Field K] [Field E] [Field F] [Field F'] [Field FE] [Field F'E]
  [Algebra K E] [Algebra K F] [Algebra K F'] [Algebra E FE] [Algebra E F'E] [Algebra K FE] [Algebra K F'E]
  [IsScalarTower K E FE] [IsScalarTower K E F'E]

noncomputable def iota (eF : E ⊗[K] F ≃ₐ[E] FE) : F →ₐ[K] FE :=
  (eF.toAlgHom.restrictScalars K).comp (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := F))

omit [IsScalarTower K E F'E] [Algebra K F'E] [Algebra E F'E] [Field F'E] [Algebra K F'] [Field F'] in
theorem iota_apply (eF : E ⊗[K] F ≃ₐ[E] FE) (f : F) : iota eF f = eF (1 ⊗ₜ f) := rfl

omit [IsScalarTower K E F'E] [Algebra K F'E] [Algebra E F'E] [Field F'E] [Algebra K F'] [Field F'] in

theorem eF_tmul (eF : E ⊗[K] F ≃ₐ[E] FE) (c : E) (f : F) : eF (c ⊗ₜ f) = c • iota eF f := by
  rw [iota_apply, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem phiE_eF (eF : E ⊗[K] F ≃ₐ[E] FE) (eF' : E ⊗[K] F' ≃ₐ[E] F'E) (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E)
    (hcomm : ∀ f, φE (iota eF f) = iota eF' (φ f)) (t : E ⊗[K] F) :
    φE (eF t) = eF' (Algebra.TensorProduct.map (AlgHom.id E E) φ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c f =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, eF_tmul, eF_tmul, map_smul, hcomm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem span_iota_basis_eq_top (eF : E ⊗[K] F ≃ₐ[E] FE) (eF' : E ⊗[K] F' ≃ₐ[E] F'E)
    (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E) (hcomm : ∀ f, φE (iota eF f) = iota eF' (φ f))
    {n : Type*} [Fintype n] (b : letI := algebraAlong φ; Module.Basis n F F') :
    letI := algebraAlong φE
    Submodule.span FE (Set.range fun i => iota eF' (b i)) = ⊤ := by
  letI := algebraAlong φ
  letI iE := algebraAlong φE
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := eF'.surjective y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul c f' =>
    rw [eF_tmul]
    have hc : ∀ z : F'E, c • z = (algebraMap E FE c) • z := fun z => by
      rw [Algebra.smul_def, Algebra.smul_def]
      change _ = φE (algebraMap E FE c) * z
      rw [AlgHom.commutes]
    rw [hc]
    refine Submodule.smul_mem _ _ ?_
    rw [← b.sum_repr f', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    change iota eF' (φ (b.repr f' i)) * iota eF' (b i) ∈ _
    rw [← hcomm]
    change (iota eF (b.repr f' i)) • iota eF' (b i) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

noncomputable def Theta (φ : F →ₐ[K] F') {n : Type*} [DecidableEq n] (b : letI := algebraAlong φ; Module.Basis n F F') :
    (n →₀ (E ⊗[K] F)) ≃ₗ[K] E ⊗[K] F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (TensorProduct.finsuppRight K K E F n).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl K E) (b.repr.restrictScalars K).symm

theorem Theta_single_tmul (φ : F →ₐ[K] F') {n : Type*} [DecidableEq n] (b : letI := algebraAlong φ; Module.Basis n F F')
    (i : n) (c : E) (f : F) :
    Theta φ b (Finsupp.single i (c ⊗ₜ f)) = c ⊗ₜ (φ f * b i) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  simp only [Theta, LinearEquiv.trans_apply, TensorProduct.finsuppRight_symm_apply_single,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.restrictScalars_symm_apply,
    Module.Basis.repr_symm_single]
  rfl

theorem eF'_Theta (eF : E ⊗[K] F ≃ₐ[E] FE) (eF' : E ⊗[K] F' ≃ₐ[E] F'E)
    (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E) (hcomm : ∀ f, φE (iota eF f) = iota eF' (φ f))
    {n : Type*} [DecidableEq n] (b : letI := algebraAlong φ; Module.Basis n F F') (t : n →₀ (E ⊗[K] F)) :
    eF' (Theta φ b t) = t.sum fun i x => φE (eF x) * iota eF' (b i) := by
  induction t using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.sum_zero_index]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, Finsupp.sum_add_index']
    · intro i; simp only [map_zero, zero_mul]
    · intro i x y; simp only [map_add, add_mul]
  | single i x =>
    rw [Finsupp.sum_single_index (by simp only [map_zero, zero_mul])]
    induction x using TensorProduct.induction_on with
    | zero => simp only [Finsupp.single_zero, map_zero, zero_mul]
    | add x y hx hy => rw [Finsupp.single_add, map_add, map_add, hx, hy, map_add, map_add, add_mul]
    | tmul c f =>
      rw [Theta_single_tmul, eF_tmul, eF_tmul, map_smul, hcomm, map_mul, smul_mul_assoc]

theorem linearIndependent_iota_basis (eF : E ⊗[K] F ≃ₐ[E] FE) (eF' : E ⊗[K] F' ≃ₐ[E] F'E)
    (φ : F →ₐ[K] F') (φE : FE →ₐ[E] F'E) (hcomm : ∀ f, φE (iota eF f) = iota eF' (φ f))
    {n : Type*} [Fintype n] [DecidableEq n] (b : letI := algebraAlong φ; Module.Basis n F F') :
    letI := algebraAlong φE
    LinearIndependent FE (fun i => iota eF' (b i)) := by
  letI iE := algebraAlong φE
  rw [Fintype.linearIndependent_iff]
  intro g hg i

  set t : n →₀ (E ⊗[K] F) := Finsupp.equivFunOnFinite.symm fun i => eF.symm (g i) with ht
  have hti : ∀ i, eF (t i) = g i := fun i => by
    simp only [ht, Finsupp.coe_equivFunOnFinite_symm, AlgEquiv.apply_symm_apply]
  have hsum : eF' (Theta φ b t) = 0 := by
    rw [eF'_Theta eF eF' φ φE hcomm b t, Finsupp.sum_fintype _ _ (fun i => by simp only [map_zero, zero_mul])]
    simp only [hti]
    rw [← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
    rfl
  have ht0 : t = 0 := (Theta φ b).injective (by rw [map_zero]; exact eF'.injective (by rw [map_zero]; exact hsum))
  rw [← hti i, ht0, Finsupp.zero_apply, map_zero]

end BasisTransport

end DiffBC

open ModularCurve DiffBC

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (hα : ∀ f : ↥(modularFunctionFieldFull p),
      heckeAlphaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f))
    (hβ : ∀ f : ↥(modularFunctionFieldFull p),
      heckeBetaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f))
    (hfin : FiniteAlong ℚ φβ.toRatAlgHom)
    (ω : Ω[↥(modularFunctionFieldFull p)⁄ℚ]) :
    ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
      (Differential.pullbackAlong
        (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p))))
        (Differential.correspondence φβ.toRatAlgHom φα.toRatAlgHom ω)) =
    heckeDiffBar p q
      (((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
            ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
        (Differential.pullbackAlong
          (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))) ω)) := by

  let eF := ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)
  let eF' := ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ)))
  have hια : ∀ f, heckeAlphaBar (AlgebraicClosure ℚ) p q (iota eF f) = iota eF' (φα.toRatAlgHom f) :=
    fun f => hα f
  have hιβ : ∀ f, heckeBetaBar (AlgebraicClosure ℚ) p q (iota eF f) = iota eF' (φβ.toRatAlgHom f) :=
    fun f => hβ f

  change kappa ℚ (AlgebraicClosure ℚ) (iota eF)
      (Differential.traceAlong φβ.toRatAlgHom (Differential.pullbackAlong φα.toRatAlgHom ω)) =
    Differential.traceAlong (heckeBetaBar (AlgebraicClosure ℚ) p q)
      (Differential.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) p q) (kappa ℚ (AlgebraicClosure ℚ) (iota eF) ω))

  letI iφ := algebraAlong φβ.toRatAlgHom
  haveI := isScalarTower_along φβ.toRatAlgHom
  haveI hfin' : Module.Finite ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldFull (p * (q : ℕ))) := hfin
  let b := Module.finBasis ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldFull (p * (q : ℕ)))
  have hb : LinearIndependent ↥(modularFunctionFieldFull p) b ∧
      Submodule.span ↥(modularFunctionFieldFull p) (Set.range b) = ⊤ := ⟨b.linearIndependent, b.span_eq⟩
  have hb' := And.intro
    (linearIndependent_iota_basis eF eF' φβ.toRatAlgHom (heckeBetaBar (AlgebraicClosure ℚ) p q) hιβ b)
    (span_iota_basis_eq_top eF eF' φβ.toRatAlgHom (heckeBetaBar (AlgebraicClosure ℚ) p q) hιβ b)

  haveI : CharZero ↥(modularFunctionFieldFull p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ ↥(modularFunctionFieldFull p)).injective
  have hφ : SeparableAlong ℚ φβ.toRatAlgHom :=
    separableAlong_of_charZero _ fun x =>
      (Algebra.IsIntegral.of_finite ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldFull (p * (q : ℕ)))).isIntegral x
  have hφE : SeparableAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) p q) := by
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) p q)
    haveI : Module.Finite ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar (p * (q : ℕ))) :=
      Module.Finite.of_basis (Module.Basis.mk hb'.1 hb'.2.ge)
    haveI : CharZero ↥(modularFunctionFieldBar p) :=
      charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)).injective
    exact separableAlong_of_charZero _ fun x =>
      (Algebra.IsIntegral.of_finite ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar (p * (q : ℕ)))).isIntegral x

  rw [kappa_traceAlong (iota eF) (iota eF') φβ.toRatAlgHom (heckeBetaBar (AlgebraicClosure ℚ) p q) hιβ hφ hφE b hb hb'
      (fun η => kappa_pullbackAlong (iota eF) (iota eF') φβ.toRatAlgHom (heckeBetaBar (AlgebraicClosure ℚ) p q) hιβ η),
    kappa_pullbackAlong (iota eF) (iota eF') φα.toRatAlgHom (heckeAlphaBar (AlgebraicClosure ℚ) p q) hια ω]

end S_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map
end P2MW
export P2MW.S_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map (solution)
