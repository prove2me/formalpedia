-- Prove2me | solution 1 for MeasureTheory.Measure.gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a165eb12-b6db-564c-ae8f-d3ead3c26fe1

import Mathlib
import Theorems.Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory P2MW.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi.MeasureTheory Set"
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory
p2m_export "MeasureTheory" "SigmaFinite Measure.IsAddHaarMeasure.sigmaFinite Measure MeasurePreserving Measure.IsAddHaarMeasure volume_pi Measure.pi Measure.pi_pi Measure.map Measure.map_apply volume_measurePreserving_piCongrLeft Measure.pi_eq measurePreserving_pi Measure.smul_apply Measure.map_smul Measure.map_map Measure.gram_smul_map_volume_eq_of_span_eq"
namespace GramTensor
p2m_open "MeasureTheory"

theorem pi_const_smul {ι α : Type} [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    (Measure.pi fun _ : ι => c • ν) = c ^ Fintype.card ι • Measure.pi fun _ : ι => ν := by
  lift c to ℝ≥0 using hc
  haveI hsf : SigmaFinite ((c : ℝ≥0∞) • ν) := (inferInstance : SigmaFinite (c • ν))
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem measurePreserving_curry (ι κ X : Type) [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X) (Measure.pi fun _ : ι × κ => ν)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν) := by
  have hsymm : MeasurePreserving (MeasurableEquiv.curry ι κ X).symm
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν) (Measure.pi fun _ : ι × κ => ν) := by
    refine ⟨(MeasurableEquiv.curry ι κ X).symm.measurable, ?_⟩
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.curry ι κ X).symm.measurable (MeasurableSet.univ_pi hs)]
    have : (MeasurableEquiv.curry ι κ X).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i : ι => Set.univ.pi fun k : κ => s (i, k) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, MeasurableEquiv.coe_curry_symm, Function.uncurry,
        Prod.forall]
    rw [this, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using hsymm.symm

variable {R : Type} [NormedCommRing R] [NormedAlgebra ℝ R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def trForm (R ι : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [Fintype ι] [DecidableEq ι] :
    LinearMap.BilinForm ℝ (Matrix ι ι R) :=
  (LinearMap.mul ℝ (Matrix ι ι R)).compr₂ ((Algebra.trace ℝ R).comp (Matrix.traceLinearMap ι ℝ R))

theorem trForm_apply (X Y : Matrix ι ι R) :
    trForm R ι X Y = Algebra.trace ℝ R (Matrix.trace (X * Y)) := rfl

def coordR {m : ℕ} (b : Fin m → R) : (Fin m → ℝ) → R := fun c => ∑ a, c a • b a

def gramR {m : ℕ} (b : Fin m → R) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a a' : Fin m => Algebra.trace ℝ R (b a * b a')

abbrev T (ι : Type) (m : ℕ) : Type := ι × ι × Fin m

def q {m : ℕ} (b : Fin m → R) : T ι m → Matrix ι ι R := fun t => Matrix.single t.1 t.2.1 (b t.2.2)

def τ (ι : Type) [Fintype ι] (m : ℕ) : T ι m ≃ Fin (Fintype.card ι * (Fintype.card ι * m)) :=
  (Equiv.prodCongr (Fintype.equivFin ι)
      ((Equiv.prodCongr (Fintype.equivFin ι) (Equiv.refl (Fin m))).trans finProdFinEquiv)).trans
    finProdFinEquiv

def p {m : ℕ} (b : Fin m → R) : Fin (Fintype.card ι * (Fintype.card ι * m)) → Matrix ι ι R :=
  fun k => q b ((τ ι m).symm k)

theorem sum_smul_q_apply {m : ℕ} (b : Fin m → R) (g : T ι m → ℝ) (j l : ι) :
    (∑ t, g t • q b t) j l = ∑ a, g (j, l, a) • b a := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, q, Matrix.single_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, smul_ite, smul_zero]
  rw [Finset.sum_eq_single j]
  · simp only [true_and]
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'
      simp [hl']
    · intro h; exact absurd (Finset.mem_univ l) h
  · intro j' _ hj'
    simp [hj']
  · intro h; exact absurd (Finset.mem_univ j) h

theorem sum_smul_q_eq {m : ℕ} (b : Fin m → R) (g : T ι m → ℝ) :
    ∑ t, g t • q b t = Matrix.of fun j l => coordR b fun a => g (j, l, a) := by
  ext j l
  rw [sum_smul_q_apply]
  rfl

theorem sum_smul_p_eq {m : ℕ} (b : Fin m → R) (c : Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ) :
    ∑ k, c k • p b k = Matrix.of fun j l => coordR b fun a => c (τ ι m (j, l, a)) := by
  rw [← sum_smul_q_eq b (fun t => c (τ ι m t))]
  exact Fintype.sum_equiv (τ ι m).symm _ _ fun k => by simp [p]

theorem linearIndependent_q {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b) :
    LinearIndependent ℝ (q b : T ι m → Matrix ι ι R) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  have h := congrFun (congrFun hg t.1) t.2.1
  rw [sum_smul_q_apply] at h
  exact Fintype.linearIndependent_iff.mp hb (fun a => g (t.1, t.2.1, a)) h t.2.2

theorem linearIndependent_p {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b) :
    LinearIndependent ℝ (p b : Fin (Fintype.card ι * (Fintype.card ι * m)) → Matrix ι ι R) :=
  (linearIndependent_q b hb).comp _ (τ ι m).symm.injective

theorem span_q {m : ℕ} (b : Fin m → R) (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    Submodule.span ℝ (Set.range (q b : T ι m → Matrix ι ι R)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ => ?_
  have hX : X j l ∈ Submodule.span ℝ (Set.range b) := by rw [hbsp]; exact Submodule.mem_top
  have hmap : Matrix.singleLinearMap ℝ j l (X j l) ∈
      (Submodule.span ℝ (Set.range b)).map (Matrix.singleLinearMap ℝ j l : R →ₗ[ℝ] Matrix ι ι R) :=
    Submodule.mem_map_of_mem hX
  rw [← Submodule.span_image] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨(j, l, a), rfl⟩

theorem span_p {m : ℕ} (b : Fin m → R) (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    Submodule.span ℝ (Set.range (p b : Fin (Fintype.card ι * (Fintype.card ι * m)) → Matrix ι ι R)) = ⊤ := by
  have : Set.range (p b : Fin (Fintype.card ι * (Fintype.card ι * m)) → Matrix ι ι R) =
      Set.range (q b : T ι m → Matrix ι ι R) :=
    (τ ι m).symm.surjective.range_comp (q b)
  rw [this, span_q b hbsp]

def P (ι : Type) [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℝ :=
  Matrix.of fun x y => if y = (x.2, x.1) then 1 else 0

theorem P_eq_permMatrix : P ι = Equiv.Perm.permMatrix ℝ (Equiv.prodComm ι ι) := by
  ext x y
  simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv, Option.mem_def, eq_comm,
    Prod.swap]

theorem abs_det_P : |(P ι).det| = 1 := by
  rw [P_eq_permMatrix, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.prodComm ι ι)) with h | h <;> simp [h]

theorem trForm_q_q {m : ℕ} (b : Fin m → R) (t t' : T ι m) :
    trForm R ι (q b t) (q b t') = P ι (t.1, t.2.1) (t'.1, t'.2.1) * gramR b t.2.2 t'.2.2 := by
  simp only [trForm_apply, q]
  rw [Matrix.trace_single_mul, Matrix.single_apply]
  simp only [P, gramR, Matrix.of_apply, Prod.mk.injEq]
  by_cases h : t'.1 = t.2.1 ∧ t'.2.1 = t.1
  · rw [if_pos h, if_pos h, one_mul, smul_eq_mul]
  · rw [if_neg h, if_neg h, zero_mul, smul_zero, map_zero]

theorem gram_q_eq_submatrix {m : ℕ} (b : Fin m → R) :
    (Matrix.of fun t t' : T ι m => trForm R ι (q b t) (q b t')) =
      (Matrix.kroneckerMap (fun x y => x * y) (P ι) (gramR b)).submatrix
        (Equiv.prodAssoc ι ι (Fin m)).symm (Equiv.prodAssoc ι ι (Fin m)).symm := by
  ext t t'
  rw [Matrix.of_apply, trForm_q_q, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  rfl

theorem abs_det_gram_q {m : ℕ} (b : Fin m → R) :
    |(Matrix.of fun t t' : T ι m => trForm R ι (q b t) (q b t')).det| =
      |(gramR b).det| ^ (Fintype.card ι * Fintype.card ι) := by
  rw [gram_q_eq_submatrix, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, abs_mul, abs_pow,
    abs_pow, abs_det_P, one_pow, one_mul, Fintype.card_prod]

theorem abs_det_gram_p {m : ℕ} (b : Fin m → R) :
    |(Matrix.of fun k k' : Fin (Fintype.card ι * (Fintype.card ι * m)) =>
        trForm R ι (p b k) (p b k')).det| =
      |(gramR b).det| ^ (Fintype.card ι * Fintype.card ι) := by
  have : (Matrix.of fun k k' : Fin (Fintype.card ι * (Fintype.card ι * m)) =>
        trForm R ι (p b k) (p b k')) =
      (Matrix.of fun t t' : T ι m => trForm R ι (q b t) (q b t')).submatrix (τ ι m).symm (τ ι m).symm := by
    ext k k'; rfl
  rw [this, Matrix.det_submatrix_equiv_self, abs_det_gram_q]

theorem sqrt_abs_det_gram_p {m : ℕ} (b : Fin m → R) :
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun k k' : Fin (Fintype.card ι * (Fintype.card ι * m)) =>
        trForm R ι (p b k) (p b k')).det|) =
      ENNReal.ofReal (Real.sqrt |(gramR b).det|) ^ (Fintype.card ι * Fintype.card ι) := by
  rw [abs_det_gram_p, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  congr 1
  have h : (Real.sqrt |(gramR b).det| ^ (Fintype.card ι * Fintype.card ι)) ^ 2 =
      |(gramR b).det| ^ (Fintype.card ι * Fintype.card ι) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (abs_nonneg _)]
  rw [← h, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]

def basisR {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    Module.Basis (Fin m) ℝ R :=
  Module.Basis.mk hb hbsp.ge

theorem finiteDimensional_of_family {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) : FiniteDimensional ℝ R :=
  Module.Finite.of_basis (basisR b hb hbsp)

theorem coordR_eq {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    haveI := finiteDimensional_of_family b hb hbsp
    coordR b = ⇑((basisR b hb hbsp).equivFunL.symm : (Fin m → ℝ) ≃L[ℝ] R) := by
  funext c
  change coordR b c = (basisR b hb hbsp).equivFun.symm c
  rw [Module.Basis.equivFun_symm_apply]
  simp [coordR, basisR, Module.Basis.coe_mk]

theorem continuous_coordR {m : ℕ} (b : Fin m → R) : Continuous (coordR b) := by
  unfold coordR
  exact continuous_finsetSum _ fun a _ => (continuous_apply a).smul continuous_const

theorem measurable_coordR {m : ℕ} (b : Fin m → R) : Measurable (coordR b) :=
  (continuous_coordR b).measurable

theorem isAddHaarMeasure_map_coordR {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    (Measure.map (coordR b) (volume : Measure (Fin m → ℝ))).IsAddHaarMeasure := by
  haveI := finiteDimensional_of_family b hb hbsp
  rw [coordR_eq b hb hbsp]
  exact ContinuousLinearEquiv.isAddHaarMeasure_map _ _

theorem sigmaFinite_map_coordR {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    SigmaFinite (Measure.map (coordR b) (volume : Measure (Fin m → ℝ))) := by
  haveI := finiteDimensional_of_family b hb hbsp
  haveI := isAddHaarMeasure_map_coordR b hb hbsp
  exact Measure.IsAddHaarMeasure.sigmaFinite _

def E (ι : Type) [Fintype ι] (m : ℕ) :
    (Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ) → (ι → ι → Fin m → ℝ) :=
  fun c => (MeasurableEquiv.piCongrRight fun _ : ι => MeasurableEquiv.curry ι (Fin m) ℝ)
    (MeasurableEquiv.curry ι (ι × Fin m) ℝ ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (τ ι m)).symm c))

theorem E_apply (m : ℕ) (c : Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ) (j l : ι) (a : Fin m) :
    E ι m c j l a = c (τ ι m (j, l, a)) := rfl

theorem measurePreserving_E (m : ℕ) :
    MeasurePreserving (E ι m) (volume : Measure (Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ))
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ))) := by
  have h1 : MeasurePreserving ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (τ ι m)).symm)
      (volume : Measure (Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ))
      (volume : Measure (T ι m → ℝ)) :=
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (τ ι m)).symm _
  have h2 : MeasurePreserving (MeasurableEquiv.curry ι (ι × Fin m) ℝ)
      (volume : Measure (T ι m → ℝ))
      (Measure.pi fun _ : ι => (volume : Measure (ι × Fin m → ℝ))) := by
    have := measurePreserving_curry ι (ι × Fin m) ℝ (volume : Measure ℝ)
    rwa [← volume_pi, ← volume_pi] at this
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : ι => MeasurableEquiv.curry ι (Fin m) ℝ)
      (Measure.pi fun _ : ι => (volume : Measure (ι × Fin m → ℝ)))
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ))) := by
    have hc : MeasurePreserving (MeasurableEquiv.curry ι (Fin m) ℝ)
        (volume : Measure (ι × Fin m → ℝ)) (Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ))) := by
      have := measurePreserving_curry ι (Fin m) ℝ (volume : Measure ℝ)
      rwa [← volume_pi, ← volume_pi] at this
    exact measurePreserving_pi (fun _ : ι => (volume : Measure (ι × Fin m → ℝ)))
      (fun _ : ι => Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ))) fun _ => hc
  exact (h3.comp h2).comp h1

theorem measurable_matrixOf [FiniteDimensional ℝ R] [MeasurableSpace (Matrix ι ι R)]
    [BorelSpace (Matrix ι ι R)] :
    Measurable (Matrix.of : (ι → ι → R) → Matrix ι ι R) :=
  (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)).measurable

theorem map_sum_smul_p_volume [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    Measure.map (fun c : Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ => ∑ k, c k • p b k) volume =
      Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
        (Measure.pi fun _ : ι => Measure.pi fun _ : ι =>
          Measure.map (coordR b) (volume : Measure (Fin m → ℝ))) := by
  haveI := finiteDimensional_of_family b hb hbsp
  haveI := sigmaFinite_map_coordR b hb hbsp

  have hfun : (fun c : Fin (Fintype.card ι * (Fintype.card ι * m)) → ℝ => ∑ k, c k • p b k) =
      (Matrix.of : (ι → ι → R) → Matrix ι ι R) ∘
        ((fun f : ι → ι → Fin m → ℝ => fun j l => coordR b (f j l)) ∘ E ι m) := by
    funext c
    rw [sum_smul_p_eq]
    rfl

  have hG : MeasurePreserving (fun f : ι → ι → Fin m → ℝ => fun j l => coordR b (f j l))
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ)))
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => Measure.map (coordR b) volume) := by
    have h0 : MeasurePreserving (coordR b) (volume : Measure (Fin m → ℝ)) (Measure.map (coordR b) volume) :=
      ⟨measurable_coordR b, rfl⟩
    have h1 : MeasurePreserving (fun g : ι → Fin m → ℝ => fun l => coordR b (g l))
        (Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ)))
        (Measure.pi fun _ : ι => Measure.map (coordR b) volume) :=
      measurePreserving_pi (fun _ : ι => (volume : Measure (Fin m → ℝ)))
        (fun _ : ι => Measure.map (coordR b) volume) fun _ => h0
    exact measurePreserving_pi (fun _ : ι => Measure.pi fun _ : ι => (volume : Measure (Fin m → ℝ)))
      (fun _ : ι => Measure.pi fun _ : ι => Measure.map (coordR b) volume) fun _ => h1
  have hGE := hG.comp (measurePreserving_E (ι := ι) m)
  rw [hfun, ← Measure.map_map measurable_matrixOf hGE.measurable, hGE.map_eq]

theorem main [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    {m : ℕ} (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤)
    (μ : Measure R) [SigmaFinite μ] (κ : ℝ≥0∞) (hκ : κ ≠ ⊤)
    (hμ : ENNReal.ofReal (Real.sqrt |(gramR b).det|) • Measure.map (coordR b) volume = κ • μ)
    {n : ℕ} (e : Fin n → Matrix ι ι R) (he : LinearIndependent ℝ e)
    (hesp : Submodule.span ℝ (Set.range e) = ⊤) :
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n => trForm R ι (e i) (e j)).det|) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume =
      κ ^ (Fintype.card ι * Fintype.card ι) •
        Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
          (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ) := by
  haveI := finiteDimensional_of_family b hb hbsp
  haveI := sigmaFinite_map_coordR b hb hbsp

  have hspan : Submodule.span ℝ (Set.range (p b : _ → Matrix ι ι R)) = Submodule.span ℝ (Set.range e) := by
    rw [span_p b hbsp, hesp]
  rw [← MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq (trForm R ι) e (p b) he
    (linearIndependent_p b hb) hspan, sqrt_abs_det_gram_p, map_sum_smul_p_volume b hb hbsp]

  have h1 : (Measure.pi fun _ : ι => ENNReal.ofReal (Real.sqrt |(gramR b).det|) •
      Measure.map (coordR b) (volume : Measure (Fin m → ℝ))) =
        Measure.pi fun _ : ι => κ • μ := by rw [hμ]
  rw [pi_const_smul _ _ ENNReal.ofReal_ne_top, pi_const_smul _ _ hκ] at h1
  have h2 : (Measure.pi fun _ : ι => ENNReal.ofReal (Real.sqrt |(gramR b).det|) ^ Fintype.card ι •
      Measure.pi fun _ : ι => Measure.map (coordR b) (volume : Measure (Fin m → ℝ))) =
        Measure.pi fun _ : ι => κ ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by rw [h1]
  rw [pi_const_smul _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    pi_const_smul _ _ (ENNReal.pow_ne_top hκ), ← pow_mul, ← pow_mul] at h2
  rw [← Measure.map_smul, h2, Measure.map_smul]

end MeasureTheory.GramTensor

end

open _root_.MeasureTheory _root_.P2MW.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi.MeasureTheory in
theorem solution
    (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [MeasurableSpace R] [BorelSpace R]
    (ι : Type) [Fintype ι] [MeasurableSpace (Matrix ι ι R)] [BorelSpace (Matrix ι ι R)]
    (m : ℕ) (b : Fin m → R) (hb : LinearIndependent ℝ b) (hbsp : Submodule.span ℝ (Set.range b) = ⊤)
    (μ : Measure R) [SigmaFinite μ] (κ : ENNReal) (hκ : κ ≠ ⊤)
    (hμ : (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ R (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume = κ • μ)
    (n : ℕ) (e : Fin n → Matrix ι ι R) (he : LinearIndependent ℝ e)
    (hesp : Submodule.span ℝ (Set.range e) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
          Algebra.trace ℝ R (Matrix.trace (e i * e j))).det|)) •
        Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume =
      κ ^ (Fintype.card ι * Fintype.card ι) •
        Measure.map (Matrix.of : (ι → ι → R) → Matrix ι ι R)
          (Measure.pi fun _ : ι => Measure.pi fun _ : ι => μ) := by
  classical
  exact MeasureTheory.GramTensor.main b hb hbsp μ κ hκ hμ e he hesp

end S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi
end P2MW
export P2MW.S_MeasureTheory_Measure_gram_trace_matrix_smul_map_volume_eq_pow_smul_map_of_pi_pi (solution)
