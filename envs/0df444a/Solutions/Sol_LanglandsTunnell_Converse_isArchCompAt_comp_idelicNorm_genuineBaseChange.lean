-- Prove2me | solution 1 for LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5f71f1d3-5712-5470-8df5-3de8558bcf23

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open scoped TensorProduct NumberField.LiesOver ComplexConjugate
open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.ComplexEmbedding
open M4aHerbrand.ArchSemilocal FLT.InfiniteAdeleBaseChange NumberField.AdelicVolume

noncomputable section

namespace ArchCompIdelicNormSol

theorem algebraMap_norm_eq_norm_equiv_one_tmul
    {R A R' A' : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
    [Module.Finite R A] [CommRing R'] [Algebra R R'] [CommRing A'] [Algebra R' A']
    (e : (R' ⊗[R] A) ≃ₐ[R'] A') (a : A) :
    algebraMap R R' (Algebra.norm R a) = Algebra.norm R' (e ((1 : R') ⊗ₜ[R] a)) := by
  rw [Algebra.norm_eq_of_algEquiv e, Algebra.norm_apply, Algebra.norm_apply,
    ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

def piSplitAtLinear {ι : Type*} [DecidableEq ι] (R : Type*) [CommRing R] (S : ι → Type*)
    [∀ j, AddCommGroup (S j)] [∀ j, Module R (S j)] (i : ι) :
    (∀ j, S j) ≃ₗ[R] S i × ∀ j : {j // j ≠ i}, S j :=
  (Equiv.piSplitAt i S).toLinearEquiv
    { map_add := fun _ _ => rfl
      map_smul := fun _ _ => rfl }

theorem norm_pi_mulSingle {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    {S : ι → Type*} [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)] [∀ j, Module.Free R (S j)]
    [∀ j, Module.Finite R (S j)] (i : ι) (x : S i) :
    Algebra.norm R (Pi.mulSingle i x : ∀ j, S j) = Algebra.norm R x := by
  classical
  let e := piSplitAtLinear R S i
  have key : e.toLinearMap ∘ₗ Algebra.lmul R (∀ j, S j) (Pi.mulSingle i x) ∘ₗ
      e.symm.toLinearMap =
        LinearMap.prodMap (Algebra.lmul R (S i) x) LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨a, g⟩
    have hsymm_i : (e.symm (a, g)) i = a := by
      show (Equiv.piSplitAt i S).symm (a, g) i = a
      simp [Equiv.piSplitAt]
    have hsymm_j : ∀ j : {j // j ≠ i}, (e.symm (a, g)) j.1 = g j := by
      intro j
      show (Equiv.piSplitAt i S).symm (a, g) j.1 = g j
      simp [Equiv.piSplitAt, j.2]
    refine Prod.ext ?_ (funext fun j => ?_)
    · show (Pi.mulSingle i x * e.symm (a, g)) i = x * a
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, hsymm_i]
    · show (Pi.mulSingle i x * e.symm (a, g)) j.1 = g j
      rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne j.2, hsymm_j, one_mul]
  rw [Algebra.norm_apply, ← LinearMap.det_conj _ e, key, LinearMap.det_prodMap,
    LinearMap.det_id, mul_one, Algebra.norm_apply]

theorem ringHom_ext_tensor {K R L T : Type*} [CommRing K] [CommRing R] [Algebra K R]
    [CommRing L] [Algebra K L] [Semiring T] {f g : (R ⊗[K] L) →+* T}
    (h₁ : ∀ r : R, f (r ⊗ₜ[K] (1 : L)) = g (r ⊗ₜ[K] (1 : L)))
    (h₂ : ∀ l : L, f ((1 : R) ⊗ₜ[K] l) = g ((1 : R) ⊗ₜ[K] l)) : f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul r l =>
    have hsplit : r ⊗ₜ[K] l = (r ⊗ₜ[K] (1 : L)) * ((1 : R) ⊗ₜ[K] l) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

section Arch

variable (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

abbrev archData : InfinitePlaceData E M := genuineInfinitePlaceData (K := E) (L := M)

abbrev evalAlgebra (v : InfinitePlace E) : Algebra (InfiniteAdeleRing E) v.Completion :=
  (evalAlgHom E v).toRingHom.toAlgebra

omit [NumberField E] in
theorem isScalarTower_eval (v : InfinitePlace E) :
    letI := evalAlgebra E v
    IsScalarTower E (InfiniteAdeleRing E) v.Completion :=
  letI := evalAlgebra E v
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem free_and_finite :
    letI := (archData E M).conorm.toAlgebra
    Module.Free (InfiniteAdeleRing E) (InfiniteAdeleRing M) ∧
      Module.Finite (InfiniteAdeleRing E) (InfiniteAdeleRing M) := by
  letI := (archData E M).adeleAlgebra
  haveI : Module.Finite E M := Module.Finite.of_restrictScalars_finite ℚ E M
  let te := (archData E M).baseChangeAlgEquiv
  exact ⟨Module.Free.of_equiv te.toLinearEquiv, Module.Finite.equiv te.toLinearEquiv⟩

def fibreEquiv (v : InfinitePlace E) :
    letI := (archData E M).conorm.toAlgebra
    letI := evalAlgebra E v
    (v.Completion ⊗[InfiniteAdeleRing E] InfiniteAdeleRing M) ≃ₐ[v.Completion]
      ((w : v.Extension M) → w.1.Completion) :=
  letI := (archData E M).adeleAlgebra
  letI := evalAlgebra E v
  haveI := isScalarTower_eval E v
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion)
      (archData E M).baseChangeAlgEquiv.symm).trans
    (Algebra.TensorProduct.cancelBaseChange E (InfiniteAdeleRing E) v.Completion v.Completion M)).trans
    (placeEquivAlg (K := E) (L := M) v)

theorem fibreEquiv_one_tmul (v : InfinitePlace E) (y : InfiniteAdeleRing M) :
    letI := (archData E M).conorm.toAlgebra
    letI := evalAlgebra E v
    fibreEquiv E M v ((1 : v.Completion) ⊗ₜ[InfiniteAdeleRing E] y) =
      fun w : v.Extension M => y w.1 := by
  letI := (archData E M).adeleAlgebra
  letI := evalAlgebra E v
  haveI := isScalarTower_eval E v

  let φ₁ : InfiniteAdeleRing M →+* ((w : v.Extension M) → w.1.Completion) :=
    (fibreEquiv E M v).toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        InfiniteAdeleRing M →ₐ[InfiniteAdeleRing E]
          v.Completion ⊗[InfiniteAdeleRing E] InfiniteAdeleRing M).toRingHom
  let φ₂ : InfiniteAdeleRing M →+* ((w : v.Extension M) → w.1.Completion) :=
    RingHom.pi fun w => (evalAlgHom M w.1).toRingHom
  suffices h : φ₁ = φ₂ by
    exact congrArg (fun φ : InfiniteAdeleRing M →+* _ => φ y) h

  let te := (archData E M).baseChangeAlgEquiv
  suffices h : φ₁.comp te.toAlgHom.toRingHom = φ₂.comp te.toAlgHom.toRingHom by
    refine RingHom.ext fun z => ?_
    have := congrArg (fun φ : (InfiniteAdeleRing E ⊗[E] M) →+* _ => φ (te.symm z)) h
    simpa using this
  refine ringHom_ext_tensor (fun r => ?_) (fun m => ?_)
  ·
    have hte : te (r ⊗ₜ[E] (1 : M)) = algebraMap (InfiniteAdeleRing E) (InfiniteAdeleRing M) r := rfl
    show φ₁ (te (r ⊗ₜ[E] (1 : M))) = φ₂ (te (r ⊗ₜ[E] (1 : M)))
    rw [hte]
    have h1 : φ₁ (algebraMap (InfiniteAdeleRing E) (InfiniteAdeleRing M) r) =
        algebraMap v.Completion _ (r v) := by
      show fibreEquiv E M v ((1 : v.Completion) ⊗ₜ[InfiniteAdeleRing E]
        (algebraMap (InfiniteAdeleRing E) (InfiniteAdeleRing M) r)) = _
      have : (1 : v.Completion) ⊗ₜ[InfiniteAdeleRing E]
          (algebraMap (InfiniteAdeleRing E) (InfiniteAdeleRing M) r) =
          algebraMap v.Completion (v.Completion ⊗[InfiniteAdeleRing E] InfiniteAdeleRing M)
            (r v) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.algebraMap_eq_smul_one r, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
        rfl
      rw [this, AlgEquiv.commutes]
    rw [h1]
    funext w
    obtain ⟨w, hw⟩ := w
    subst hw
    show _ = (archData E M).conorm r w
    rw [Pi.algebraMap_apply]
    haveI : w.1.LiesOver (w.comap (algebraMap E M)).1 := liesOver_of_comap_eq rfl
    show _ = psiFactor (w.comap (algebraMap E M)) w ((r (w.comap (algebraMap E M))) ⊗ₜ[E] (1 : M))
    rw [psiFactor_tmul, map_one, mul_one]
  ·
    have hte : te ((1 : InfiniteAdeleRing E) ⊗ₜ[E] m) = algebraMap M (InfiniteAdeleRing M) m :=
      (archData E M).baseChangeAlgEquiv_one_tmul m
    show φ₁ (te ((1 : InfiniteAdeleRing E) ⊗ₜ[E] m)) = φ₂ (te ((1 : InfiniteAdeleRing E) ⊗ₜ[E] m))
    have h2 : φ₂ (te ((1 : InfiniteAdeleRing E) ⊗ₜ[E] m)) =
        fun w : v.Extension M => algebraMap M w.1.Completion m := by
      rw [hte]; rfl
    rw [h2]
    show placeEquivAlg (K := E) (L := M) v
      (Algebra.TensorProduct.cancelBaseChange E (InfiniteAdeleRing E) v.Completion v.Completion M
        (Algebra.TensorProduct.congr AlgEquiv.refl te.symm
          ((1 : v.Completion) ⊗ₜ[InfiniteAdeleRing E] (te ((1 : InfiniteAdeleRing E) ⊗ₜ[E] m))))) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp only [AlgEquiv.coe_algHom, AlgEquiv.coe_refl, AlgEquiv.symm_apply_apply]
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    funext w
    show psi (K := E) (L := M) v ((1 : v.Completion) ⊗ₜ[E] m) w = _
    rw [psi_apply, psiFactor_one_tmul]

theorem archNorm_apply (y : InfiniteAdeleRing M) (v : InfinitePlace E) :
    (letI := (archData E M).conorm.toAlgebra;
      Algebra.norm (InfiniteAdeleRing E) y) v =
      Algebra.norm v.Completion (fun w : v.Extension M => y w.1) := by
  letI := (archData E M).adeleAlgebra
  letI := evalAlgebra E v
  haveI := isScalarTower_eval E v
  haveI := (free_and_finite E M).1
  haveI := (free_and_finite E M).2
  have h := algebraMap_norm_eq_norm_equiv_one_tmul (fibreEquiv E M v) y
  rw [fibreEquiv_one_tmul] at h
  exact h

omit [NumberField E] [NumberField M] in

theorem liesOver_comap (w' : InfinitePlace M) : w'.1.LiesOver (w'.comap (algebraMap E M)).1 :=
  liesOver_of_comap_eq rfl

attribute [local instance] liesOver_comap

theorem idelicNorm_archUnitHom (w' : InfinitePlace M) (x : (w'.Completion)ˣ) :
    (genuineBaseChange E M).idelicNorm (archUnitHom w' x) =
      archUnitHom (w'.comap (algebraMap E M))
        (Units.map (Algebra.norm (w'.comap (algebraMap E M)).Completion :
          w'.Completion →* (w'.comap (algebraMap E M)).Completion) x) := by
  classical
  set y : AdeleRing (𝓞 M) M := ((archCentralUnit M w' x : (AdeleRing (𝓞 M) M)ˣ) : AdeleRing (𝓞 M) M)
    with hy
  have hcw := M4aHerbrand.genuineAdelicNorm_componentwise E M y
  have hy1 : y.1 = Function.update (1 : InfiniteAdeleRing M) w' (x : w'.Completion) := rfl
  refine Units.ext (Prod.ext ?_ ?_)
  ·
    show ((genuineBaseChange E M).adelicNorm y).1 = _
    refine hcw.1.trans (funext fun v₀ => (archNorm_apply E M y.1 v₀).trans ?_)
    by_cases hv : v₀ = w'.comap (algebraMap E M)
    · subst hv
      rw [archUnitHom_apply, archCentralUnit_fst_self, Units.coe_map]
      haveI : ∀ w : (w'.comap (algebraMap E M)).Extension M,
          FiniteDimensional (w'.comap (algebraMap E M)).Completion w.1.Completion :=
        fun w => finiteDimensional_completion _ w.1
      haveI : ∀ w : (w'.comap (algebraMap E M)).Extension M,
          Module.Free (w'.comap (algebraMap E M)).Completion w.1.Completion :=
        fun w => Module.Free.of_divisionRing _ _
      have hfun : (fun w : (w'.comap (algebraMap E M)).Extension M => y.1 w.1) =
          Pi.mulSingle (⟨w', rfl⟩ : (w'.comap (algebraMap E M)).Extension M) (x : w'.Completion) := by
        rw [hy1]
        exact Function.update_comp_eq_of_injective' (1 : (w : InfinitePlace M) → w.Completion)
          Subtype.val_injective (⟨w', rfl⟩ : (w'.comap (algebraMap E M)).Extension M)
          (x : w'.Completion)
      rw [hfun, norm_pi_mulSingle]
    · rw [archUnitHom_apply, archCentralUnit_fst_of_ne _ _ hv]
      have hfun : (fun w : v₀.Extension M => y.1 w.1) = 1 := by
        funext w
        have hne : w.1 ≠ w' := by
          intro h
          exact hv (by rw [← w.2, h])
        rw [hy1, Function.update_of_ne hne]
        rfl
      rw [hfun, map_one]
  ·
    show ((genuineBaseChange E M).adelicNorm y).2 = (1 : FiniteAdeleRing (𝓞 E) E)
    apply RestrictedProduct.ext
    intro v
    refine (hcw.2 v).trans ?_
    refine Finset.prod_eq_one fun w _ => ?_
    have h2 : (y.2 : FiniteAdeleRing (𝓞 M) M) w.1 = 1 := rfl
    rw [h2, map_one]

theorem archLocalChar_comp_idelicNorm (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M)
    (x : (w'.Completion)ˣ) :
    archLocalChar (μ.comp (genuineBaseChange E M).idelicNorm) w' x =
      archLocalChar μ (w'.comap (algebraMap E M))
        (Units.map (Algebra.norm (w'.comap (algebraMap E M)).Completion :
          w'.Completion →* (w'.comap (algebraMap E M)).Completion) x) := by
  show μ ((genuineBaseChange E M).idelicNorm (archUnitHom w' x)) = μ (archUnitHom _ _)
  rw [idelicNorm_archUnitHom]

theorem norm_eq_norm_extensionEmbedding {K : Type*} [Field K] (w : InfinitePlace K)
    (z : w.Completion) : ‖z‖ = ‖extensionEmbedding w z‖ :=
  ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z).symm

omit [NumberField E] [NumberField M] in

theorem exists_eq_algebraMap_of_isUnramified (w' : InfinitePlace M)
    (h : w'.IsReal ∨ (w'.comap (algebraMap E M)).IsComplex) (x : w'.Completion) :
    ∃ y : (w'.comap (algebraMap E M)).Completion,
      algebraMap _ w'.Completion y = x ∧
        Algebra.norm (w'.comap (algebraMap E M)).Completion x = y := by
  have h1 : Module.finrank (w'.comap (algebraMap E M)).Completion w'.Completion = 1 :=
    finrank_eq_one_of_isUnramified _ (InfinitePlace.isUnramified_iff.mpr h)
  obtain ⟨y, hy⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1).2 x
  refine ⟨y, hy, ?_⟩
  rw [← hy, Algebra.norm_algebraMap, h1, pow_one]

omit [NumberField E] [NumberField M] in

theorem extensionEmbedding_algebraMap_of_isReal (w' : InfinitePlace M)
    (hw : (w'.comap (algebraMap E M)).IsReal) (y : (w'.comap (algebraMap E M)).Completion) :
    extensionEmbedding w' (algebraMap _ w'.Completion y) =
      extensionEmbedding (w'.comap (algebraMap E M)) y := by
  haveI := LiesOver.extensionEmbedding_liesOver_of_isReal w' hw
  exact liesOver_extensionEmbedding_apply w' _

omit [NumberField E] [NumberField M] in

theorem extensionEmbedding_algebraMap_or_conj (w' : InfinitePlace M)
    (y : (w'.comap (algebraMap E M)).Completion) :
    extensionEmbedding w' (algebraMap _ w'.Completion y) =
        extensionEmbedding (w'.comap (algebraMap E M)) y ∨
      conj (extensionEmbedding w' (algebraMap _ w'.Completion y)) =
        extensionEmbedding (w'.comap (algebraMap E M)) y := by
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w'
      (w'.comap (algebraMap E M)) with hl | hr
  · haveI : ComplexEmbedding.LiesOver w'.embedding (w'.comap (algebraMap E M)).embedding := ⟨hl⟩
    haveI := liesOver_extensionEmbedding w' (w'.comap (algebraMap E M))
    exact Or.inl (liesOver_extensionEmbedding_apply w' _)
  · haveI : ComplexEmbedding.LiesOver (conjugate w'.embedding)
        (w'.comap (algebraMap E M)).embedding := ⟨hr⟩
    haveI := liesOver_conjugate_extensionEmbedding w' (w'.comap (algebraMap E M))
    refine Or.inr ?_
    rw [← conjugate_coe_eq]
    exact liesOver_extensionEmbedding_apply w' _

omit [NumberField E] [NumberField M] in

private theorem _root_.ArchCompIdelicNormSol.norm_algebraMap (w' : InfinitePlace M) (y : (w'.comap (algebraMap E M)).Completion) :
    ‖algebraMap _ w'.Completion y‖ = ‖y‖ := by
  rw [norm_eq_norm_extensionEmbedding, norm_eq_norm_extensionEmbedding _ y]
  rcases extensionEmbedding_algebraMap_or_conj E M w' y with h | h
  · rw [h]
  · rw [← h, Complex.norm_conj]

p2m_export "ArchCompIdelicNormSol" "norm_algebraMap"
omit [NumberField E] [NumberField M] in

theorem extensionEmbedding_norm_of_isRamified (w' : InfinitePlace M) (hw' : w'.IsComplex)
    (hw : (w'.comap (algebraMap E M)).IsReal) (x : w'.Completion) :
    extensionEmbedding (w'.comap (algebraMap E M))
        (Algebra.norm (w'.comap (algebraMap E M)).Completion x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  haveI := LiesOver.extensionEmbedding_liesOver_of_isReal w' hw
  have he : RingHom.comp (algebraMap ℝ ℂ) (ringEquivRealOfIsReal hw : _ →+* ℝ) =
      RingHom.comp (ringEquivComplexOfIsComplex hw' : w'.Completion →+* ℂ)
        (algebraMap (w'.comap (algebraMap E M)).Completion w'.Completion) := by
    ext y
    simp
  have key := Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hw)
    (ringEquivComplexOfIsComplex hw') he x
  rw [key, ← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw,
    RingEquiv.apply_symm_apply, Algebra.norm_complex_apply, ringEquivComplexOfIsComplex_apply,
    Complex.normSq_eq_norm_sq, ← norm_eq_norm_extensionEmbedding]

theorem conj_div_norm_eq_inv (z : ℂ) (hz : z ≠ 0) :
    conj z / (‖z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [inv_div, div_eq_div_iff hn hz, Complex.conj_mul', sq]

theorem clause_real (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M) (u : ℂ)
    (hw' : w'.IsReal) (a : ℤ) (h : IsArchCompAt E μ (w'.comap (algebraMap E M)) u a) :
    IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u a := by
  intro x
  rw [archLocalChar_comp_idelicNorm, h, Units.coe_map]
  obtain ⟨y, hyx, hny⟩ := exists_eq_algebraMap_of_isUnramified E M w' (Or.inl hw') (x : w'.Completion)
  rw [hny, ← hyx, norm_algebraMap, extensionEmbedding_algebraMap_of_isReal E M w' (hw'.comap _),
    mult_isReal ⟨w', hw'⟩, mult_isReal ⟨_, hw'.comap _⟩]

theorem clause_ramified (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M) (u : ℂ)
    (hw' : w'.IsComplex) (hw : (w'.comap (algebraMap E M)).IsReal) (a : ℤ)
    (h : IsArchCompAt E μ (w'.comap (algebraMap E M)) u a) :
    IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u 0 := by
  intro x
  rw [archLocalChar_comp_idelicNorm, h, Units.coe_map, zpow_zero, mul_one,
    mult_isReal ⟨_, hw⟩, mult_isComplex ⟨w', hw'⟩, Nat.cast_one, one_mul, Nat.cast_two]
  have hx0 : (x : w'.Completion) ≠ 0 := x.ne_zero
  have hnx : 0 < ‖(x : w'.Completion)‖ := norm_pos_iff.mpr hx0
  have hE : extensionEmbedding (w'.comap (algebraMap E M))
      (Algebra.norm (w'.comap (algebraMap E M)).Completion (x : w'.Completion)) =
        ((‖(x : w'.Completion)‖ ^ 2 : ℝ) : ℂ) :=
    extensionEmbedding_norm_of_isRamified E M w' hw' hw x
  have hN : ‖Algebra.norm (w'.comap (algebraMap E M)).Completion (x : w'.Completion)‖ =
      ‖(x : w'.Completion)‖ ^ 2 := by
    rw [norm_eq_norm_extensionEmbedding, hE, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
  rw [hN, hE]
  have hr0 : ((‖(x : w'.Completion)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos hnx 2).ne'
  rw [div_self hr0, one_zpow, mul_one]

  have hlog : (Complex.log (‖(x : w'.Completion)‖ : ℂ) * 2).im = 0 := by
    rw [← Complex.ofReal_log hnx.le, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  rw [Complex.cpow_mul u (by rw [hlog]; exact neg_lt_zero.mpr Real.pi_pos)
    (by rw [hlog]; exact Real.pi_pos.le), Complex.cpow_two]
  push_cast
  ring

theorem clause_complex (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M) (u : ℂ)
    (hw' : w'.IsComplex) (hw : (w'.comap (algebraMap E M)).IsComplex) (k : ℤ)
    (h : IsArchCompAt E μ (w'.comap (algebraMap E M)) u k) :
    IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u k ∨
      IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u (-k) := by

  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w'
      (w'.comap (algebraMap E M)) with hl | hr
  · haveI : ComplexEmbedding.LiesOver w'.embedding (w'.comap (algebraMap E M)).embedding := ⟨hl⟩
    haveI := liesOver_extensionEmbedding w' (w'.comap (algebraMap E M))
    refine Or.inl fun x => ?_
    rw [archLocalChar_comp_idelicNorm, h, Units.coe_map]
    obtain ⟨y, hyx, hny⟩ :=
      exists_eq_algebraMap_of_isUnramified E M w' (Or.inr hw) (x : w'.Completion)
    rw [hny, ← hyx, norm_algebraMap, liesOver_extensionEmbedding_apply w',
      mult_isComplex ⟨w', hw'⟩, mult_isComplex ⟨_, hw⟩]
  · haveI : ComplexEmbedding.LiesOver (conjugate w'.embedding)
        (w'.comap (algebraMap E M)).embedding := ⟨hr⟩
    haveI := liesOver_conjugate_extensionEmbedding w' (w'.comap (algebraMap E M))
    refine Or.inr fun x => ?_
    rw [archLocalChar_comp_idelicNorm, h, Units.coe_map]
    obtain ⟨y, hyx, hny⟩ :=
      exists_eq_algebraMap_of_isUnramified E M w' (Or.inr hw) (x : w'.Completion)
    have hconj : extensionEmbedding (w'.comap (algebraMap E M)) y =
        conj (extensionEmbedding w' (algebraMap _ w'.Completion y)) := by
      have h' : conjugate (extensionEmbedding w') (algebraMap _ w'.Completion y) =
          extensionEmbedding (w'.comap (algebraMap E M)) y :=
        liesOver_extensionEmbedding_apply w' _
      rw [← h']
      rfl
    rw [hny, ← hyx, norm_algebraMap, hconj, mult_isComplex ⟨w', hw'⟩, mult_isComplex ⟨_, hw⟩,
      norm_eq_norm_extensionEmbedding _ y, hconj, Complex.norm_conj]
    have hz : extensionEmbedding w' (algebraMap _ w'.Completion y) ≠ 0 := by
      rw [hyx]
      exact (map_ne_zero _).mpr x.ne_zero
    rw [conj_div_norm_eq_inv _ hz, inv_zpow']

end Arch

end ArchCompIdelicNormSol

end

open ArchCompIdelicNormSol in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w' : InfinitePlace M) (u : ℂ) :
    (∀ (_ : w'.IsReal) (a : ℤ), IsArchCompAt E μ (w'.comap (algebraMap E M)) u a →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u a) ∧
    (∀ (_ : w'.IsComplex) (_ : (w'.comap (algebraMap E M)).IsReal) (a : ℤ),
        IsArchCompAt E μ (w'.comap (algebraMap E M)) u a →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u 0) ∧
    (∀ (_ : w'.IsComplex) (_ : (w'.comap (algebraMap E M)).IsComplex) (k : ℤ),
        IsArchCompAt E μ (w'.comap (algebraMap E M)) u k →
        IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u k ∨
          IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' u (-k)) :=
  ⟨fun hw' a h => clause_real E M μ w' u hw' a h,
    fun hw' hw a h => clause_ramified E M μ w' u hw' hw a h,
    fun hw' hw k h => clause_complex E M μ w' u hw' hw k h⟩

end S_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
end P2MW
export P2MW.S_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange (solution)
