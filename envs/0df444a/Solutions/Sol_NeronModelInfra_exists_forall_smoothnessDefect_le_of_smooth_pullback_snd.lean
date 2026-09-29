-- Prove2me | solution 1 for NeronModelInfra.exists_forall_smoothnessDefect_le_of_smooth_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7d175bfd-9aee-5076-8e73-48932069b256

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

universe v w

open TensorProduct IsLocalRing

noncomputable section

namespace NeronSmootheningBound

section TorsionExponent

variable {S : Type u} [CommRing S] [IsDomain S]
variable {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module S F₁] [AddCommGroup F₀] [Module S F₀]

theorem smul_eq_zero_of_mem_torsion_of_comp_comp_eq_smul [Module.IsTorsionFree S F₀]
    (N : F₁ →ₗ[S] F₀) (H : F₀ →ₗ[S] F₁) (r : S) (hH : N ∘ₗ H ∘ₗ N = r • N)
    (x : F₀ ⧸ LinearMap.range N) (hx : x ∈ Submodule.torsion S (F₀ ⧸ LinearMap.range N)) :
    r • x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨s, hs⟩, hsx⟩ := (Submodule.mem_torsion_iff _).mp hx

  have hsx' : (s : S) • x ∈ LinearMap.range N := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hsx
  obtain ⟨y, hy⟩ := hsx'

  have key : s • (r • x - N (H x)) = 0 := by
    have h1 : N (H (N y)) = r • N y := by
      have := congrArg (fun φ => φ y) hH
      simpa using this
    rw [smul_sub, smul_comm s r x, ← hy, ← h1, hy, LinearMap.map_smul, LinearMap.map_smul]
    exact sub_self _
  have hs0 : (s : S) ≠ 0 := nonZeroDivisors.ne_zero hs
  have : r • x - N (H x) = 0 := by
    rcases smul_eq_zero.mp key with h | h
    · exact absurd h hs0
    · exact h
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨H x, (sub_eq_zero.mp this).symm⟩

end TorsionExponent

section LengthBound

variable {S : Type u} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem length_quotient_span_pow (ϖ : S) (hϖ : Irreducible ϖ) (c : ℕ) :
    Module.length S (S ⧸ Ideal.span {ϖ ^ c}) = c := by
  have : Ideal.span {ϖ ^ c} = maximalIdeal S ^ c := by
    rw [← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]
  rw [this]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal S c

variable {C : Type v} [AddCommGroup C] [Module S C]

omit [IsDiscreteValuationRing S] in

theorem torsion_inf_pow_smul_eq_bot (ϖ : S) (c : ℕ)
    (hkill : ∀ x ∈ Submodule.torsion S C, ϖ ^ c • x = 0) :
    Submodule.torsion S C ⊓ (Ideal.span {ϖ ^ c} • ⊤ : Submodule S C) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, ht'⟩
  rw [Submodule.mem_bot]
  rw [Submodule.ideal_span_singleton_smul, SetLike.mem_coe, Submodule.mem_smul_pointwise_iff_exists] at ht'
  obtain ⟨y, -, rfl⟩ := ht'

  by_cases hc : ϖ ^ c = 0
  · simp [hc]
  have hy : y ∈ Submodule.torsion S C := by
    obtain ⟨⟨s, hs⟩, hsy⟩ := (Submodule.mem_torsion_iff _).mp ht
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s * ϖ ^ c, ?_⟩, ?_⟩
    · exact mul_mem_nonZeroDivisors.mpr ⟨hs, mem_nonZeroDivisors_of_ne_zero hc⟩
    · change (s * ϖ ^ c) • y = 0
      rw [mul_smul]; exact hsy
  exact hkill y hy

theorem length_torsion_le (ϖ : S) (hϖ : Irreducible ϖ) (c n : ℕ)
    (g : (Fin n → S) →ₗ[S] C) (hg : Function.Surjective g)
    (hkill : ∀ x ∈ Submodule.torsion S C, ϖ ^ c • x = 0) :
    Module.length S (Submodule.torsion S C) ≤ (n * c : ℕ) := by
  classical
  set I : Ideal S := Ideal.span {ϖ ^ c} with hI

  have hinj : Function.Injective ((I • (⊤ : Submodule S C)).mkQ ∘ₗ (Submodule.torsion S C).subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ht
    have : (t : C) ∈ Submodule.torsion S C ⊓ (I • ⊤ : Submodule S C) := ⟨t.2, ht⟩
    rw [torsion_inf_pow_smul_eq_bot ϖ c hkill, Submodule.mem_bot] at this
    exact (Submodule.mem_bot S).mpr (Subtype.ext this)
  have h1 := Module.length_le_of_injective _ hinj

  let m : Fin n → C ⧸ (I • (⊤ : Submodule S C)) := fun i => Submodule.Quotient.mk (g (Pi.single i 1))
  have hm : ∀ i, I ≤ LinearMap.ker (LinearMap.toSpanSingleton S _ (m i)) := by
    intro i r hr
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    change r • Submodule.Quotient.mk _ = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let φ : Fin n → ((S ⧸ I) →ₗ[S] C ⧸ (I • (⊤ : Submodule S C))) := fun i => I.liftQ _ (hm i)
  let ψ : (Fin n → S ⧸ I) →ₗ[S] C ⧸ (I • (⊤ : Submodule S C)) := ∑ i, φ i ∘ₗ LinearMap.proj i
  have hφ : ∀ (i : Fin n) (s : S), φ i (Submodule.Quotient.mk s) = s • m i := by
    intro i s
    simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
  have hψv : ∀ v : Fin n → S, ψ (fun i => Submodule.Quotient.mk (v i)) = Submodule.Quotient.mk (g v) := by
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : S) := by
      ext j; simp [Pi.single_apply, Finset.sum_apply]
    simp only [ψ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, hφ, m]
    conv_rhs => rw [hv, map_sum]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨v, rfl⟩ := ((Submodule.mkQ_surjective _).comp hg) z
    exact ⟨fun i => Submodule.Quotient.mk (v i), by rw [hψv]; rfl⟩
  have h2 := Module.length_le_of_surjective _ hψ
  have h3 : Module.length S (Fin n → S ⧸ I) = (n * c : ℕ) := by
    rw [Module.length_pi_of_fintype]
    have : Module.length S (S ⧸ I) = c := length_quotient_span_pow ϖ hϖ c
    rw [this]
    simp
  calc Module.length S (Submodule.torsion S C)
      ≤ Module.length S (C ⧸ (I • (⊤ : Submodule S C))) := h1
    _ ≤ Module.length S (Fin n → S ⧸ I) := h2
    _ = (n * c : ℕ) := h3

end LengthBound

section GeneralizedInverse

open TensorProduct

variable {A : Type u} [CommRing A]

theorem exists_comp_comp_eq_self_of_projective_coker
    {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module A F₁] [AddCommGroup F₀] [Module A F₀]
    [Module.Projective A F₀] (N : F₁ →ₗ[A] F₀)
    [Module.Projective A (F₀ ⧸ LinearMap.range N)] :
    ∃ H : F₀ →ₗ[A] F₁, N ∘ₗ H ∘ₗ N = N := by
  set q : F₀ →ₗ[A] F₀ ⧸ LinearMap.range N := (LinearMap.range N).mkQ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id) (Submodule.mkQ_surjective _)

  set e : F₀ →ₗ[A] F₀ := LinearMap.id - s ∘ₗ q
  have he : ∀ y, e y ∈ LinearMap.range N := by
    intro y
    have : q (e y) = 0 := by
      simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
      have := congrArg (fun φ => φ (q y)) hs
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this, sub_self]
    rwa [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  have heN : ∀ z, e (N z) = N z := by
    intro z
    simp only [e, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    have : q (N z) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨z, rfl⟩
    rw [this, map_zero, sub_zero]
  let e' : F₀ →ₗ[A] LinearMap.range N := LinearMap.codRestrict _ e he
  obtain ⟨H, hH⟩ := Module.projective_lifting_property N.rangeRestrict e' N.surjective_rangeRestrict
  refine ⟨H, ?_⟩
  ext z
  have := congrArg (fun φ => ((φ (N z) : LinearMap.range N) : F₀)) hH
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, e'] at this
  simp only [LinearMap.comp_apply]
  rw [this, heN]

variable (π : A) (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away π B]

noncomputable def baseChangeCokerEquiv (Q : Type u) [CommRing Q] [Algebra A Q]
    {F₁ : Type v} {F₀ : Type w} [AddCommGroup F₁] [Module A F₁] [AddCommGroup F₀] [Module A F₀]
    (N : F₁ →ₗ[A] F₀) :
    ((Q ⊗[A] F₀) ⧸ LinearMap.range (N.baseChange Q)) ≃ₗ[Q] Q ⊗[A] (F₀ ⧸ LinearMap.range N) := by
  refine (LinearMap.range (N.baseChange Q)).quotEquivOfEq _ ?_ ≪≫ₗ
    ((LinearMap.range N).mkQ.baseChange Q).quotKerEquivOfSurjective ?_
  ·
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : (LinearMap.range N).mkQ ∘ₗ N = 0 := by ext; simp
      rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply]
    · intro x hx
      have hx' : x ∈ LinearMap.ker (((LinearMap.range N).mkQ).lTensor Q) := hx
      rw [lTensor_mkQ] at hx'
      obtain ⟨y, rfl⟩ := hx'
      obtain ⟨w, rfl⟩ := (LinearMap.lTensor_surjective Q N.surjective_rangeRestrict) y
      refine ⟨w, ?_⟩
      change (N.lTensor Q) w = _
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]; rfl
  · exact LinearMap.lTensor_surjective Q (Submodule.mkQ_surjective _)

end GeneralizedInverse

section ClearDenominators

open TensorProduct

variable {A : Type u} [CommRing A] (π : A) (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away π B]

theorem exists_pow_smul_eq_zero_of_baseChange_eq_zero {n m : ℕ}
    (D : (Fin m → A) →ₗ[A] (Fin n → A)) (hD : D.baseChange B = 0) :
    ∃ k : ℕ, (π ^ k) • D = 0 := by
  classical

  have hentry : ∀ i j, algebraMap A B (LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n)) D i j)
      = 0 := by
    intro i j
    have h := LinearMap.toMatrix_baseChange (A := B) D (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n))
    have := congrArg (fun M => M i j) h
    simp only [hD, map_zero, Matrix.zero_apply, Matrix.map_apply] at this
    exact this.symm
  have hk : ∀ ij : Fin n × Fin m, ∃ k : ℕ, π ^ k *
      LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n)) D ij.1 ij.2 = 0 := by
    intro ij
    obtain ⟨⟨b, hb⟩, hb'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers π) B _).mp (hentry ij.1 ij.2)
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hb
    exact ⟨k, hb'⟩
  choose k hk using hk
  refine ⟨∑ ij, k ij, ?_⟩
  apply (LinearMap.toMatrix (Pi.basisFun A (Fin m)) (Pi.basisFun A (Fin n))).injective
  rw [map_smul, map_zero]
  ext i j
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
  have hle : k (i, j) ≤ ∑ ij, k ij := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, add_comm, pow_add, mul_assoc, hk (i, j), mul_zero]

theorem exists_pow_smul_eq_baseChange {n m : ℕ}
    (H : (B ⊗[A] (Fin n → A)) →ₗ[B] (B ⊗[A] (Fin m → A))) :
    ∃ (c : ℕ) (H₀ : (Fin n → A) →ₗ[A] (Fin m → A)), H₀.baseChange B = (algebraMap A B (π ^ c)) • H := by
  classical
  let bn := Algebra.TensorProduct.basis B (Pi.basisFun A (Fin n))
  let bm := Algebra.TensorProduct.basis B (Pi.basisFun A (Fin m))
  let M : Matrix (Fin m) (Fin n) B := LinearMap.toMatrix bn bm H
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers π)
    (fun ij : Fin m × Fin n => M ij.1 ij.2)
  obtain ⟨c, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hb
  choose a ha using fun ij : Fin m × Fin n => hint ij
  let M₀ : Matrix (Fin m) (Fin n) A := fun i j => a (i, j)
  refine ⟨c, Matrix.toLin (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin m)) M₀, ?_⟩
  apply (LinearMap.toMatrix bn bm).injective
  rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin, map_smul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, M₀]
  rw [ha (i, j)]
  simp [M, Algebra.smul_def]

theorem exists_comp_comp_eq_pow_smul {n m : ℕ}
    (N : (Fin m → A) →ₗ[A] (Fin n → A))
    [Module.Projective B (B ⊗[A] ((Fin n → A) ⧸ LinearMap.range N))] :
    ∃ (c : ℕ) (H : (Fin n → A) →ₗ[A] (Fin m → A)), N ∘ₗ H ∘ₗ N = (π ^ c) • N := by
  classical
  haveI : Module.Projective B ((B ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange B)) :=
    Module.Projective.of_equiv (baseChangeCokerEquiv B N).symm
  obtain ⟨HB, hHB⟩ := exists_comp_comp_eq_self_of_projective_coker (A := B) (N.baseChange B)
  obtain ⟨c, H₀, hH₀⟩ := exists_pow_smul_eq_baseChange π B HB

  have hz : (N ∘ₗ H₀ ∘ₗ N - (π ^ c) • N).baseChange B = 0 := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_comp, LinearMap.baseChange_comp, hH₀,
      LinearMap.baseChange_smul, LinearMap.smul_comp, LinearMap.comp_smul, hHB, algebraMap_smul]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply]
    exact sub_self _
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_baseChange_eq_zero π B _ hz
  refine ⟨k + c, (π ^ k) • H₀, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hk
  rw [LinearMap.smul_comp, LinearMap.comp_smul, hk]

end ClearDenominators

section Core

open TensorProduct

theorem length_torsion_eq_of_equiv {S : Type u} [CommRing S] {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
    Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
  have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
    constructor
    · rintro ⟨x, ⟨a, ha⟩, rfl⟩
      refine ⟨a, ?_⟩
      change (a : S) • (e : M →ₗ[S] M') x = 0
      change (a : S) • x = 0 at ha
      rw [← map_smul, ha, map_zero]
    · rintro ⟨a, ha⟩
      refine ⟨e.symm y, ⟨a, ?_⟩, by simp⟩
      change (a : S) • e.symm y = 0
      change (a : S) • y = 0 at ha
      rw [← map_smul, ha, map_zero]
  rw [← this]
  exact (e.submoduleMap (Submodule.torsion S M)).length_eq

theorem exists_bound_length_torsion_baseChange_kaehlerDifferential
    {R : Type u} [CommRing R] [IsNoetherianRing R] (π : R)
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away (algebraMap R A π) B]
    [Module.Projective B (B ⊗[A] Ω[A⁄R])] :
    ∃ C : ℕ, ∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra A S],
      Irreducible (algebraMap A S (algebraMap R A π)) →
      Module.length S (Submodule.torsion S (S ⊗[A] Ω[A⁄R])) ≤ C := by
  classical
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  haveI : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite A _
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin A Ω[A⁄R]
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let N : (Fin m → A) →ₗ[A] (Fin n → A) := Fintype.linearCombination A s
  have hN : LinearMap.range N = K := by rw [Fintype.range_linearCombination, hs]

  let eN : ((Fin n → A) ⧸ LinearMap.range N) ≃ₗ[A] Ω[A⁄R] :=
    (Submodule.quotEquivOfEq _ _ hN).trans e.symm
  haveI : Module.Projective B (B ⊗[A] ((Fin n → A) ⧸ LinearMap.range N)) :=
    Module.Projective.of_equiv (eN.baseChange A B _ _ ).symm
  obtain ⟨c, H, hH⟩ := exists_comp_comp_eq_pow_smul (algebraMap R A π) B N
  refine ⟨n * c, fun S _ _ _ _ hπ => ?_⟩

  set ϖ : S := algebraMap A S (algebraMap R A π) with hϖ
  have hHS : N.baseChange S ∘ₗ H.baseChange S ∘ₗ N.baseChange S = (ϖ ^ c) • N.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hH, LinearMap.baseChange_smul]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hϖ, ← map_pow (algebraMap A S), algebraMap_smul (A := S)]
  have hkill : ∀ x ∈ Submodule.torsion S ((S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S)),
      ϖ ^ c • x = 0 :=
    fun x hx => smul_eq_zero_of_mem_torsion_of_comp_comp_eq_smul _ _ _ hHS x hx

  let g : (Fin n → S) →ₗ[S] (S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S) :=
    (LinearMap.range (N.baseChange S)).mkQ ∘ₗ (TensorProduct.piScalarRight A S S (Fin n)).symm.toLinearMap
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (TensorProduct.piScalarRight A S S (Fin n)).symm.surjective
  have hle := length_torsion_le ϖ hπ c n g hg hkill

  have eS : ((S ⊗[A] (Fin n → A)) ⧸ LinearMap.range (N.baseChange S)) ≃ₗ[S] S ⊗[A] Ω[A⁄R] :=
    (baseChangeCokerEquiv S N).trans (eN.baseChange A S _ _)
  rw [← length_torsion_eq_of_equiv eS]
  exact hle

end Core

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)

abbrev globalAlgebra : Algebra R Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

abbrev globalPointAlgebra : Algebra Γ(X, ⊤) R' :=
  ((Scheme.stalkClosedPointTo a).hom.comp
    (X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom).toAlgebra

theorem smoothnessDefect_eq_length_torsion_global [IsAffine X] :
    smoothnessDefect f a =
      (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
       letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
       Module.length R' (Submodule.torsion R' (R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]))) := by
  rw [smoothnessDefect_def]

  set x : X := a (IsLocalRing.closedPoint R') with hx
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  letI iRO : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  letI iOR' : Algebra (X.presheaf.stalk x) R' := pointAlgebra a
  letI iAO : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI : IsScalarTower R Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) R' :=
    IsScalarTower.of_algebraMap_eq' rfl

  haveI : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  haveI : Algebra.FormallyEtale Γ(X, ⊤) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal.primeCompl)

  let e₁ : (X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, ⊤) (X.presheaf.stalk x)
  let e₂ : R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] ≃ₗ[R']
      R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    (e₁.symm.baseChange (X.presheaf.stalk x) R' _ _)
  let e₃ : R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) ≃ₗ[R']
      R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, ⊤) (X.presheaf.stalk x) R' R' Ω[Γ(X, ⊤)⁄R]
  exact length_torsion_eq_of_equiv' (e₂.trans e₃)
where

  length_torsion_eq_of_equiv' {S : Type u} [CommRing S] {M M' : Type u}
      [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
      Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
    have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
      ext y
      simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
      constructor
      · rintro ⟨x, ⟨a, ha⟩, rfl⟩
        refine ⟨a, ?_⟩
        change (a : S) • (e : M →ₗ[S] M') x = 0
        change (a : S) • x = 0 at ha
        rw [← map_smul, ha, map_zero]
      · rintro ⟨a, ha⟩
        refine ⟨e.symm y, ⟨a, ?_⟩, by simp⟩
        change (a : S) • e.symm y = 0
        change (a : S) • y = 0 at ha
        rw [← map_smul, ha, map_zero]
    rw [← this]
    exact (e.submoduleMap (Submodule.torsion S M)).length_eq

theorem algebraMap_globalPointAlgebra_globalAlgebra [Algebra R R']
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) (r : R) :
    (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
     letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
     algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) r)) = algebraMap R R' r := by
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r

  have h1 := Scheme.Hom.germ_stalkMap_apply f ⊤ (a (IsLocalRing.closedPoint R')) trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ (f ⁻¹ᵁ ⊤) (a (IsLocalRing.closedPoint R')) trivial).hom
    ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r
  rw [← h1]

  rw [← CommRingCat.comp_apply, ← Scheme.stalkClosedPointTo_comp]
  have key : ∀ (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      g = Spec.map (CommRingCat.ofHom (algebraMap R R')) → ∀ s,
      (Scheme.stalkClosedPointTo g).hom
        (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint R')) trivial).hom s) =
        algebraMap R R' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
    rintro g rfl s
    have h3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap R R'))
    have := congrArg (fun φ : (Spec (CommRingCat.of R)).presheaf.obj (Opposite.op ⊤) ⟶ CommRingCat.of R' =>
      φ.hom s) h3
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  refine (key (a ≫ f) ha _).trans ?_
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

section Away

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalization_away_of_irreducible (π : R) (hπ : Irreducible π) : IsLocalization.Away π K where
  map_units := by
    rintro ⟨s, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hπ.ne_zero)))
  surj := by
    intro z
    obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors R) z
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
    refine ⟨⟨a * (v⁻¹ : Rˣ), ⟨π ^ n, n, rfl⟩⟩, ?_⟩
    have hvinv : algebraMap R K (v⁻¹ : Rˣ) * algebraMap R K (v : Rˣ) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only at hz ⊢
    calc z * algebraMap R K (π ^ n)
        = z * algebraMap R K (π ^ n) * (algebraMap R K (v⁻¹ : Rˣ) * algebraMap R K (v : Rˣ)) := by
          rw [hvinv, mul_one]
      _ = z * algebraMap R K (b : R) * algebraMap R K (v⁻¹ : Rˣ) := by rw [hv, map_mul]; ring
      _ = algebraMap R K (a * (v⁻¹ : Rˣ)) := by rw [hz, map_mul]
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using (IsFractionRing.injective R K) h⟩

end Away

section GenericFibreSmooth

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (K : Type u) [CommRing K] [Algebra R K]

abbrev globalAlgebra' : Algebra R Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

theorem eq_isoSpec_hom_comp_Spec_map [IsAffine X] :
    (letI : Algebra R Γ(X, ⊤) := globalAlgebra' f
     f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) := by
  letI : Algebra R Γ(X, ⊤) := globalAlgebra' f
  have h1 : CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := rfl
  rw [h1, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
    Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

theorem projective_baseChange_kaehlerDifferential_of_smooth_genericFibre [IsAffine X]
    (hK : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    (letI : Algebra R Γ(X, ⊤) := globalAlgebra' f
     Module.Projective (Γ(X, ⊤) ⊗[R] K) ((Γ(X, ⊤) ⊗[R] K) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R])) := by
  letI : Algebra R Γ(X, ⊤) := globalAlgebra' f
  set A : Type u := Γ(X, ⊤) with hA
  letI : Algebra K (A ⊗[R] K) := Algebra.TensorProduct.rightAlgebra

  have hf := eq_isoSpec_hom_comp_Spec_map f
  have hf' : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ 𝟙 _ = X.isoSpec.inv ≫ f := by
    rw [Category.comp_id, hf, Iso.inv_hom_id_assoc]
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) f (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    X.isoSpec.inv (𝟙 _) (𝟙 _) hf' (by simp)
  have hm : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      m ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [pullback.lift_snd, Category.comp_id]
  haveI := hK
  have h2 : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [hm]; infer_instance

  have h3 : Smooth (Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) : K →ₐ[R] A ⊗[R] K) : K →+* A ⊗[R] K))) := by
    have := pullbackSpecIso_hom_snd R A K
    have e : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) : K →ₐ[R] A ⊗[R] K) : K →+* A ⊗[R] K))
        = (pullbackSpecIso R A K).inv ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
      rw [← this, Iso.inv_hom_id_assoc]
    rw [e]; infer_instance

  have h4 : RingHom.Smooth ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) : K →ₐ[R] A ⊗[R] K) : K →+* A ⊗[R] K) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h3
  have h5 : Algebra.Smooth K (A ⊗[R] K) := h4
  haveI : Algebra.FormallySmooth K (A ⊗[R] K) := h5.formallySmooth
  haveI : Module.Projective (A ⊗[R] K) Ω[A ⊗[R] K⁄K] := Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Algebra.IsPushout R K A (A ⊗[R] K) := Algebra.IsPushout.symm inferInstance
  exact Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R K A (A ⊗[R] K)).symm

end GenericFibreSmooth

theorem irreducible_algebraMap_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (h : IsIndexOneExtension R R') (π : R) (hπ : Irreducible π) :
    Irreducible (algebraMap R R' π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← h.map_maximalIdeal, hπ, Ideal.map_span, Set.image_singleton]

theorem finiteType_appTop_comp {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).FiniteType := by
  have h : f.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹_›
  exact h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)

section Invariance

open TensorProduct

theorem smoothnessDefect_comp_eq {R : Type u} [CommRing R] {U X : Scheme.{u}} (g : U ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ U) [IsIso (g.stalkMap (a (IsLocalRing.closedPoint R')))] :
    smoothnessDefect (g ≫ f) a = smoothnessDefect f (a ≫ g) := by
  rw [smoothnessDefect_def, smoothnessDefect_def]
  set p : U := a (IsLocalRing.closedPoint R') with hp
  change _ = (letI : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
    letI : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
    Module.length R' (Submodule.torsion R' (R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R])))
  letI iRO : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
  letI iOR' : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
  letI iRO' : Algebra R (U.presheaf.stalk p) := stalkAlgebra (g ≫ f) p
  letI iO'R' : Algebra (U.presheaf.stalk p) R' := pointAlgebra a
  letI iOO' : Algebra (X.presheaf.stalk (g p)) (U.presheaf.stalk p) := (g.stalkMap p).hom.toAlgebra
  haveI : IsScalarTower R (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change stalkAlgebraMap (g ≫ f) p r = (g.stalkMap p).hom (stalkAlgebraMap f (g p) r)
      rw [stalkAlgebraMap_apply, stalkAlgebraMap_apply, Scheme.Hom.germ_stalkMap_apply g ⊤ p trivial]
      rfl)
  haveI : IsScalarTower (X.presheaf.stalk (g p)) (U.presheaf.stalk p) R' :=
    IsScalarTower.of_algebraMap_eq' (by
      change (Scheme.stalkClosedPointTo (a ≫ g)).hom = (Scheme.stalkClosedPointTo a).hom.comp (g.stalkMap p).hom
      rw [Scheme.stalkClosedPointTo_comp]
      rfl)
  haveI : IsLocalization.Away (1 : X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (g.stalkMap p))
  haveI : Algebra.FormallyEtale (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : X.presheaf.stalk (g p)))
  let e₁ : (U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R] ≃ₗ[U.presheaf.stalk p]
      Ω[U.presheaf.stalk p⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (X.presheaf.stalk (g p)) (U.presheaf.stalk p)
  let e₂ : R' ⊗[U.presheaf.stalk p] Ω[U.presheaf.stalk p⁄R] ≃ₗ[R']
      R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R]) :=
    (e₁.symm.baseChange (U.presheaf.stalk p) R' _ _)
  let e₃ : R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R])
      ≃ₗ[R'] R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk (g p)) (U.presheaf.stalk p) R' R'
      Ω[X.presheaf.stalk (g p)⁄R]
  exact length_torsion_eq_of_equiv (e₂.trans e₃)

end Invariance

section Affine

theorem bound_of_isAffine {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (hK : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ a : Spec (CommRingCat.of R') ⟶ X, a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
        smoothnessDefect f a ≤ c := by
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  haveI : Algebra.FiniteType R Γ(X, ⊤) := finiteType_appTop_comp f
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI := isLocalization_away_of_irreducible K π hπ
  haveI : IsLocalization.Away (algebraMap R Γ(X, ⊤) π) (Γ(X, ⊤) ⊗[R] K) :=
    IsLocalization.Away.tensor (S := Γ(X, ⊤)) π K
  haveI : Module.Projective (Γ(X, ⊤) ⊗[R] K) ((Γ(X, ⊤) ⊗[R] K) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    projective_baseChange_kaehlerDifferential_of_smooth_genericFibre f K hK
  obtain ⟨C, hC⟩ := exists_bound_length_torsion_baseChange_kaehlerDifferential π (A := Γ(X, ⊤))
    (Γ(X, ⊤) ⊗[R] K)
  refine ⟨C, fun R' _ _ _ _ h a ha => ?_⟩
  rw [smoothnessDefect_eq_length_torsion_global f a]
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  have hirr : Irreducible (algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) π)) := by
    rw [algebraMap_globalPointAlgebra_globalAlgebra f a ha π,
      IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span, Set.image_singleton]
  exact_mod_cast hC R' hirr

end Affine

end NeronSmootheningBound

open NeronSmootheningBound in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
        smoothnessDefect f x.1 ≤ c  := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have hsm : ∀ i, Smooth (pullback.snd (𝒰.f i ≫ f) (specGenericFibreInclusion R K)) := by
    intro i
    rw [← pullbackRightPullbackFstIso_inv_snd_snd f (specGenericFibreInclusion R K) (𝒰.f i)]
    haveI := hK
    infer_instance
  have hb : ∀ i, ∃ c : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
      ∀ a : Spec (CommRingCat.of R') ⟶ 𝒰.X i, a ≫ (𝒰.f i ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
        smoothnessDefect (𝒰.f i ≫ f) a ≤ c := fun i =>
    bound_of_isAffine K (𝒰.f i ≫ f) (by simpa only [specGenericFibreInclusion_eq] using hsm i)
  choose c hc using hb
  refine ⟨∑ i, c i, fun R' _ _ _ _ h x => ?_⟩
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (x.1 (IsLocalRing.closedPoint R'))
  have hrange : Set.range x.1 ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨z, rfl⟩
    have hz : x.1 z ⤳ x.1 (IsLocalRing.closedPoint R') :=
      (IsLocalRing.specializes_closedPoint z).map x.1.continuous
    exact (𝒰.f i).isOpenEmbedding.isOpen_range.stableUnderGeneralization hz ⟨y, hy⟩
  let a' := IsOpenImmersion.lift (𝒰.f i) x.1 hrange
  have ha' : a' ≫ 𝒰.f i = x.1 := IsOpenImmersion.lift_fac _ _ _
  have h1 : smoothnessDefect f x.1 = smoothnessDefect (𝒰.f i ≫ f) a' := by
    rw [← ha', smoothnessDefect_comp_eq]
  have h2 := hc i R' h a' (by rw [← Category.assoc, ha']; exact x.2)
  rw [h1]
  refine h2.trans ?_
  exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i)

end

end S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd
end P2MW
export P2MW.S_NeronModelInfra_exists_forall_smoothnessDefect_le_of_smooth_pullback_snd (solution)
