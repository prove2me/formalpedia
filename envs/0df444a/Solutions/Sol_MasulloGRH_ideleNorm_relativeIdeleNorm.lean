-- Prove2me | solution 1 for MasulloGRH.ideleNorm_relativeIdeleNorm
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:33:32.650841+00:00
-- url     : https://prove2.me/submissions/b446d259-b781-4eee-831c-9996ebe88e40

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg

open NumberField

set_option autoImplicit false

namespace Sol_MasulloGRH_ideleNorm_relativeIdeleNorm

/-! ### Archimedean local identity -/

section ArchLocal

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

theorem norm_algebraMap_completion (c : v.Completion) :
    ‖algebraMap v.Completion w.Completion c‖ = ‖c‖ := by
  induction c using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_norm.comp (continuous_algebraMap v.Completion w.Completion))
      continuous_norm
  | ih a =>
    rw [NumberField.InfinitePlace.Completion.algebraMap_coe, Completion.norm_coe, Completion.norm_coe]
    have h := (LiesOver.isometry_algebraMap w v).norm_map_of_map_zero (map_zero _) a
    exact h

theorem norm_algebraNorm_completion (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ = ‖x‖ ^ Module.finrank v.Completion w.Completion := by
  rcases w.isUnramified_or_isRamified K with h | h
  · have h1 : Module.finrank v.Completion w.Completion = 1 := h.finrank_eq_one v
    have hx : x ∈ (⊥ : Subalgebra v.Completion w.Completion) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one h1]
      exact Algebra.mem_top
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hx
    rw [Algebra.norm_algebraMap, h1, pow_one, pow_one, norm_algebraMap_completion]
  · have h2 : Module.finrank v.Completion w.Completion = 2 := h.finrank_eq_two v
    have H := NumberField.InfinitePlace.isRamified_iff.mp h
    rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
    have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
    rw [Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext; simp) x, h2]
    have e1 : ∀ r : ℝ, ‖(ringEquivRealOfIsReal H.2).symm r‖ = ‖r‖ := by
      intro r
      have := (isometry_extensionEmbeddingOfIsReal H.2).norm_map_of_map_zero (map_zero _)
        ((ringEquivRealOfIsReal H.2).symm r)
      rw [← this, ← ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]
    have e2 : ‖ringEquivComplexOfIsComplex H.1 x‖ = ‖x‖ :=
      (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    rw [e1, Algebra.norm_complex_apply, Real.norm_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, e2]

theorem norm_algebraNorm_completion_pow_mult (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ ^ v.mult = ‖x‖ ^ w.mult := by
  rw [norm_algebraNorm_completion, ← pow_mul, mul_comm, mult_mul_finrank v w]

end ArchLocal

/-! ### Non-archimedean local identity -/

section FinLocal

open IsDedekindDomain WithZeroMulInt
open scoped NNReal WithZero

theorem toNNReal_congr {e e' : ℝ≥0} (he : e ≠ 0) (he' : e' ≠ 0) (h : e = e') (x : ℤᵐ⁰) :
    toNNReal he x = toNNReal he' x := by
  subst h; rfl

theorem toNNReal_pow_base {e : ℝ≥0} (he : e ≠ 0) (n : ℕ) (hn : n ≠ 0) (x : ℤᵐ⁰) :
    toNNReal (pow_ne_zero n he) x = toNNReal he x ^ n := by
  by_cases hx : x = 0
  · rw [toNNReal_pos_apply _ hx, toNNReal_pos_apply _ hx, zero_pow hn]
  · rw [toNNReal_neg_apply _ hx, toNNReal_neg_apply _ hx, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem norm_algebraNorm_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (y : w.1.adicCompletion L) :
    ‖Algebra.norm (v.adicCompletion K) y‖ = ‖y‖ := by
  have : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have hf : Ideal.inertiaDeg' v.asIdeal w.1.asIdeal ≠ 0 :=
    (Ideal.inertiaDeg'_pos' v.asIdeal w.1.asIdeal).ne'
  have habs : (Ideal.absNorm w.1.asIdeal : ℝ≥0) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^ Ideal.inertiaDeg' v.asIdeal w.1.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot]
    push_cast
    rfl
  rw [FinitePlace.norm_def, FinitePlace.norm_def,
    M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg K L v w y, map_pow,
    toNNReal_congr (HeightOneSpectrum.absNorm_ne_zero w.1)
      (pow_ne_zero _ (HeightOneSpectrum.absNorm_ne_zero v)) habs,
    toNNReal_pow_base _ _ hf]

end FinLocal

/-! ### Finite products over the fibres of a map -/

section Fiberwise

theorem finprod_fiberwise {α β M : Type*} [CommMonoid M] (p : α → β)
    [∀ b, Fintype {a // p a = b}] (f : α → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ b, ∏ a : {a // p a = b}, f a.1 = ∏ᶠ a, f a := by
  classical
  have hs : Function.mulSupport f ⊆ (hf.toFinset : Set α) := by simp
  have hfib : ∀ b, ∏ a : {a // p a = b}, f a.1 =
      ∏ a ∈ hf.toFinset.filter (fun a => p a = b), f a := by
    intro b
    have h1 : ∏ a : {a // p a = b}, f a.1 =
        ∏ a ∈ (Finset.univ : Finset {a // p a = b}).map (Function.Embedding.subtype _), f a := by
      rw [Finset.prod_map]; rfl
    rw [h1]
    refine (Finset.prod_subset ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_map]
      exact ⟨⟨a, ha.2⟩, Finset.mem_univ _, rfl⟩
    · intro a ha hna
      rw [Finset.mem_map] at ha
      obtain ⟨⟨a', ha'⟩, -, rfl⟩ := ha
      by_contra hne
      exact hna (Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hne, ha'⟩)
  rw [finprod_eq_prod_of_mulSupport_subset f hs,
    ← Finset.prod_fiberwise_of_maps_to (t := hf.toFinset.image p)
      (fun a ha => Finset.mem_image_of_mem p ha) f,
    finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset.image p)]
  · exact Finset.prod_congr rfl (fun b _ => hfib b)
  · intro b hb
    rw [Function.mem_mulSupport, hfib] at hb
    by_contra hbt
    apply hb
    apply Finset.prod_eq_one
    intro a ha
    exfalso
    exact hbt (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩))

end Fiberwise

/-! ### Ideles have absolute value one at almost all finite places -/

section Support

open IsDedekindDomain

variable (L : Type*) [Field L] [NumberField L]

theorem finite_mulSupport_norm_idele (g : (AdeleRing (𝓞 L) L)ˣ) :
    (Function.mulSupport
      fun w : HeightOneSpectrum (𝓞 L) => ‖(g : AdeleRing (𝓞 L) L).2 w‖).Finite := by
  have h1 := RestrictedProduct.eventually _ _ (g : AdeleRing (𝓞 L) L).2
  have h2 := RestrictedProduct.eventually _ _
    ((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
  have h := h1.and h2
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro w hw
  rw [Function.mem_mulSupport] at hw
  rw [Set.mem_ofPred_eq]
  rintro ⟨ha, hb⟩
  apply hw
  have hmul : (g : AdeleRing (𝓞 L) L).2 w *
      ((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = 1 :=
    congrArg (fun x : AdeleRing (𝓞 L) L => x.2 w) g.mul_inv
  have hn : ‖(g : AdeleRing (𝓞 L) L).2 w‖ *
      ‖((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have ha' : ‖(g : AdeleRing (𝓞 L) L).2 w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ha)
  have hb' : ‖((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hb)
  refine le_antisymm ha' ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 L) L).2 w‖ *
        ‖((g⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w‖ := hn.symm
    _ ≤ ‖(g : AdeleRing (𝓞 L) L).2 w‖ * 1 := mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ = ‖(g : AdeleRing (𝓞 L) L).2 w‖ := mul_one _

end Support

/-! ### The norm of a finite product of algebras -/

section NormPi

theorem norm_transport {ι R S R' S' : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S'] [Algebra R' S']
    (bS : Module.Basis ι R S) (c : Module.Basis ι R' S') (π : R →+* R') (P : S →+* S')
    (hP : ∀ (r : R) (s : S), P (r • s) = π r • P s) (hb : ∀ i, P (bS i) = c i) (x : S) :
    π (Algebra.norm R x) = Algebra.norm R' (P x) := by
  rw [Algebra.norm_eq_matrix_det bS, Algebra.norm_eq_matrix_det c, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have hx : P x * c j = ∑ k, π (bS.repr (x * bS j) k) • c k := by
    rw [← hb j, ← map_mul]
    conv_lhs => rw [← bS.sum_repr (x * bS j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, hb]
  rw [hx, c.repr_sum_self]

universe u v

def piMap {R : Type*} [CommRing R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M i) : (∀ i, M i) →ₗ[R] (∀ i, M i) :=
  LinearMap.pi fun i => (f i).comp (LinearMap.proj i)

theorem det_piMap {R : Type*} [CommRing R] (ι₀ : Type u) [Fintype ι₀] :
    ∀ {M : ι₀ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
      (f : ∀ i, M i →ₗ[R] M i), (piMap f).det = ∏ i, (f i).det := by
  refine Fintype.induction_empty_option
    (P := fun γ instγ =>
      ∀ {M : γ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
        [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
        (f : ∀ i, M i →ₗ[R] M i),
        (piMap f).det = (@Finset.univ γ instγ).prod fun i => (f i).det)
    ?of_equiv ?h_empty ?h_option ι₀
  case of_equiv =>
    intro α β _ e ih M _ _ _ _ f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := LinearEquiv.piCongrLeft R M e
    have hE : ∀ (y : ∀ a, M (e a)) (a), E y (e a) = y a := fun y a =>
      show Equiv.piCongrLeft M e y (e a) = y a from Equiv.piCongrLeft_apply_apply M e y a
    have hEs : ∀ (x : ∀ b, M b) (a), E.symm x a = x (e a) := fun x a =>
      show Equiv.piCongrLeft' M e.symm x a = x (e a) from rfl
    have hconj : piMap f
        = (E : (∀ a, M (e a)) →ₗ[R] ∀ b, M b) ∘ₗ (piMap fun a => f (e a))
            ∘ₗ (E.symm : (∀ b, M b) →ₗ[R] ∀ a, M (e a)) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      show f (e a) (x (e a)) = E ((piMap fun a => f (e a)) (E.symm x)) (e a)
      rw [hE]
      show f (e a) (x (e a)) = f (e a) (E.symm x a)
      rw [hEs]
    rw [hconj, LinearMap.det_conj, ih]
    exact Fintype.prod_equiv e (fun a => (f (e a)).det) (fun b => (f b).det) fun a => rfl
  case h_empty =>
    intro M _ _ _ _ f
    haveI : Subsingleton (∀ i : PEmpty, M i) := ⟨fun a b => funext fun i => i.elim⟩
    rw [LinearMap.det_eq_one_of_subsingleton, Finset.prod_of_isEmpty]
  case h_option =>
    intro α _ ih M _ _ _ _ f
    let E : (M none × ∀ a, M (some a)) ≃ₗ[R] ∀ i, M i :=
      (LinearEquiv.piOptionEquivProd R).symm
    have hconj : piMap f
        = (E : _ →ₗ[R] ∀ i, M i) ∘ₗ ((f none).prodMap (piMap fun a => f (some a)))
            ∘ₗ (E.symm : (∀ i, M i) →ₗ[R] _) := by
      apply LinearMap.ext
      intro x
      funext i
      cases i <;> rfl
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, ih, Fintype.prod_option]

theorem norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  have hl : Algebra.lmul R (∀ i, S i) x = piMap fun i => Algebra.lmul R (S i) (x i) := by
    apply LinearMap.ext
    intro y
    rfl
  rw [Algebra.norm_apply, hl, det_piMap]
  rfl

end NormPi

/-! ### The archimedean component of the adelic norm -/

section ArchGlobal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false

open NumberField.InfinitePlace M4aHerbrand M4aHerbrand.ArchSemilocal
open scoped TensorProduct NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def piBasisInf (v : InfinitePlace K) :
    Module.Basis (Fin (Module.finrank K L)) v.Completion (∀ w : v.Extension L, w.1.Completion) :=
  (Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv

theorem piBasisInf_apply (v : InfinitePlace K) (i : Fin (Module.finrank K L)) :
    piBasisInf K L v i =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) (Module.finBasis K L i) := by
  show ((Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  funext w
  show psi (K := K) (L := L) v ((1 : v.Completion) ⊗ₜ[K] Module.finBasis K L i) w = _
  rw [psi_apply, psiFactor_one_tmul]
  rfl

theorem conorm_apply_ext (x : InfiniteAdeleRing K) (v : InfinitePlace K) (w : v.Extension L) :
    (genuineInfinitePlaceData (K := K) (L := L)).conorm x w.1 =
      algebraMap v.Completion w.1.Completion (x v) := by
  obtain ⟨w, rfl⟩ := w
  haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  show psiFactor (w.comap (algebraMap K L)) w ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [psiFactor_tmul, map_one, mul_one]

noncomputable def projInfPlace (v : InfinitePlace K) :
    InfiniteAdeleRing L →+* (∀ w : v.Extension L, w.1.Completion) :=
  RingHom.pi fun w => Pi.evalRingHom (fun w' : InfinitePlace L => w'.Completion) w.1

omit [NumberField K] [NumberField L] in
theorem projInfPlace_apply (v : InfinitePlace K) (x : InfiniteAdeleRing L) (w : v.Extension L) :
    projInfPlace K L v x w = x w.1 := rfl

noncomputable def infBasis :
    letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra
    Module.Basis (Fin (Module.finrank K L)) (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra
  (Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Module.finBasis K L)).map
    (genuineInfinitePlaceData (K := K) (L := L)).baseChangeAlgEquiv.toLinearEquiv

theorem infBasis_apply (i : Fin (Module.finrank K L)) :
    (letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra; infBasis K L i)
      = algebraMap L (InfiniteAdeleRing L) (Module.finBasis K L i) := by
  letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra
  show ((Algebra.TensorProduct.basis (InfiniteAdeleRing K) (Module.finBasis K L)).map
    (genuineInfinitePlaceData (K := K) (L := L)).baseChangeAlgEquiv.toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  exact (genuineInfinitePlaceData (K := K) (L := L)).baseChangeAlgEquiv_one_tmul _

theorem projInfPlace_algebraMap (v : InfinitePlace K) (l : L) :
    projInfPlace K L v (algebraMap L (InfiniteAdeleRing L) l) =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) l := by
  funext w
  rw [projInfPlace_apply, Pi.algebraMap_apply]
  rfl

theorem projInfPlace_smul (v : InfinitePlace K) (r : InfiniteAdeleRing K)
    (s : InfiniteAdeleRing L) :
    projInfPlace K L v ((genuineInfinitePlaceData (K := K) (L := L)).conorm r * s) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) (r v) *
        projInfPlace K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projInfPlace_apply, Pi.algebraMap_apply]
  exact conorm_apply_ext K L r v w

theorem infNorm_apply (x : InfiniteAdeleRing L) (v : InfinitePlace K)
    [Fintype (v.Extension L)] :
    (letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra;
      Algebra.norm (InfiniteAdeleRing K) x) v =
      ∏ w : v.Extension L, Algebra.norm v.Completion (x w.1) := by
  classical
  letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra
  have h1 : (Algebra.norm (InfiniteAdeleRing K) x) v =
      Algebra.norm v.Completion (projInfPlace K L v x) :=
    norm_transport (infBasis K L) (piBasisInf K L v)
      (Pi.evalRingHom (fun v' : InfinitePlace K => v'.Completion) v) (projInfPlace K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projInfPlace_smul K L v r s)
      (fun i => by rw [infBasis_apply, piBasisInf_apply, projInfPlace_algebraMap]) x
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [h1, norm_pi]
  rfl

end ArchGlobal

/-! ### Assembling the local identities -/

section Main

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField.InfinitePlace M4aHerbrand M4aHerbrand.ArchSemilocal
  M4aHerbrand.Bridge
open scoped NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem prod_infinite (y : AdeleRing (𝓞 L) L) :
    ∏ v : InfinitePlace K,
        ‖((letI := (genuineβ K L).toAlgebra; Algebra.norm (AdeleRing (𝓞 K) K) y).1 :
          InfiniteAdeleRing K) v‖ ^ v.mult
      = ∏ w : InfinitePlace L, ‖y.1 w‖ ^ w.mult := by
  classical
  obtain ⟨h1, -⟩ := M4aHerbrand.genuineAdelicNorm_componentwise K L y
  rw [h1]
  have hv : ∀ v : InfinitePlace K,
      ‖(letI := (genuineInfinitePlaceData (K := K) (L := L)).conorm.toAlgebra;
          Algebra.norm (InfiniteAdeleRing K) y.1) v‖ ^ v.mult
        = ∏ w : v.Extension L, ‖y.1 w.1‖ ^ w.1.mult := by
    intro v
    rw [infNorm_apply K L y.1 v, norm_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => norm_algebraNorm_completion_pow_mult v w.1 (y.1 w.1)
  rw [Finset.prod_congr rfl fun v _ => hv v,
    Finset.prod_sigma' Finset.univ (fun v : InfinitePlace K => (Finset.univ : Finset (v.Extension L)))
      (fun v w => ‖y.1 w.1‖ ^ w.1.mult), Finset.univ_sigma_univ]
  exact Fintype.prod_equiv
    (Equiv.sigmaFiberEquiv fun w : InfinitePlace L => w.comap (algebraMap K L)) _ _ (fun _ => rfl)

theorem finprod_finite (g : (AdeleRing (𝓞 L) L)ˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ‖((letI := (genuineβ K L).toAlgebra;
          Algebra.norm (AdeleRing (𝓞 K) K) (g : AdeleRing (𝓞 L) L)).2 :
            FiniteAdeleRing (𝓞 K) K) v‖
      = ∏ᶠ w : HeightOneSpectrum (𝓞 L), ‖(g : AdeleRing (𝓞 L) L).2 w‖ := by
  obtain ⟨-, h2⟩ := M4aHerbrand.genuineAdelicNorm_componentwise K L (g : AdeleRing (𝓞 L) L)
  letI inst : ∀ v : HeightOneSpectrum (𝓞 K),
      Fintype {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  rw [← finprod_fiberwise (HeightOneSpectrum.under (𝓞 K)) _ (finite_mulSupport_norm_idele L g)]
  refine finprod_congr fun v => ?_
  letI instv : Fintype (v.Extension (𝓞 L)) :=
    HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have h : ((letI := (genuineβ K L).toAlgebra;
        Algebra.norm (AdeleRing (𝓞 K) K) (g : AdeleRing (𝓞 L) L)).2 : FiniteAdeleRing (𝓞 K) K) v
      = ∏ w : v.Extension (𝓞 L),
          Algebra.norm (v.adicCompletion K) ((g : AdeleRing (𝓞 L) L).2 w.1) := h2 v
  rw [h, norm_prod]
  exact Finset.prod_congr rfl fun w _ => norm_algebraNorm_adicCompletion K L v w _

theorem main (g : MasulloGRH.IdeleGroup L) :
    MasulloGRH.ideleNorm ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm g) =
      MasulloGRH.ideleNorm g := by
  unfold MasulloGRH.ideleNorm
  congr 1
  · exact prod_infinite K L (g : AdeleRing (𝓞 L) L)
  · exact finprod_finite K L g

end Main

end Sol_MasulloGRH_ideleNorm_relativeIdeleNorm

open MasulloGRH

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : IdeleGroup L) :
    ideleNorm ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm g) =
      ideleNorm g :=
  Sol_MasulloGRH_ideleNorm_relativeIdeleNorm.main K L g
