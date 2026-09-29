-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0a0b2b62-251f-5f78-a59d-9ecf3a970a37

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped Classical

namespace GJA

theorem exists_finset_apply_eq_sum_eval {G : Type*} (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (ℓ : (G → ℂ) →ₗ[ℂ] ℂ) :
    ∃ (T : Finset G) (a : G → ℂ), ∀ v ∈ W, ℓ v = ∑ x ∈ T, a x * v x := by
  classical
  let L : G → (W →ₗ[ℂ] ℂ) := fun g => (LinearMap.proj g).comp W.subtype
  let K : W →ₗ[ℂ] ℂ := ℓ.comp W.subtype
  have hker : ⨅ g, LinearMap.ker (L g) ≤ LinearMap.ker K := by
    intro v hv
    have h0 : (v : G → ℂ) = 0 := by
      funext g
      have := (Submodule.mem_iInf _).1 hv g
      simpa [L] using this
    rw [LinearMap.mem_ker]
    simp [K, h0]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  refine ⟨c.support, fun x => c x, fun v hv => ?_⟩
  have := congrArg (fun f : W →ₗ[ℂ] ℂ => f ⟨v, hv⟩) hc
  simp only [Finsupp.sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, L, K,
    LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, smul_eq_mul] at this
  exact this.symm

theorem translate_mem_span {G : Type*} [Group G] (w : G → ℂ)
    (v : G → ℂ) (hv : v ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) (k : G) :
    (fun x => v (x * k)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine Submodule.subset_span ⟨k * h, ?_⟩
    funext g
    simp [mul_assoc]
  | zero =>
    have h0 : (fun x => (0 : G → ℂ) (x * k)) = 0 := by funext; simp
    rw [h0]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have h1 : (fun g => (x + y) (g * k)) = (fun g => x (g * k)) + (fun g => y (g * k)) := by funext; simp
    rw [h1]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : (fun g => (a • x) (g * k)) = a • (fun g => x (g * k)) := by funext; simp
    rw [h1]; exact Submodule.smul_mem _ a hx

theorem exists_open_stabilizer_of_mem_span {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (w : G → ℂ) (hw : ∀ k ∈ K, ∀ g : G, w (g * k) = w g)
    (v : G → ℂ) (hv : v ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, v (g * k) = v g := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      have : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) =
          (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set G) := by
        ext k; simp [Subgroup.mem_comap, MulAut.conj_apply]
      rw [this]; exact hK.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ K := by
        simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
      have := hw _ hk' (g * h)
      simp only [← mul_assoc, mul_inv_cancel_right] at this
      simpa [mul_assoc] using this
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.1 hk).1, h₂ k (Subgroup.mem_inf.1 hk).2]
  | smul a x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply]; rw [h k hk]⟩

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_finset_coset_decomposition (Ω Ω' : Subgroup G) (hle : Ω' ≤ Ω)
    (hΩo : IsOpen (Ω : Set G)) (hΩc : IsCompact (Ω : Set G)) (hΩ'o : IsOpen (Ω' : Set G)) :
    ∃ T : Finset G, (↑T ⊆ (Ω : Set G)) ∧
      (Set.PairwiseDisjoint (↑T : Set G) (fun t => (fun x => t * x) '' (Ω' : Set G))) ∧
      (Ω : Set G) = ⋃ t ∈ T, (fun x => t * x) '' (Ω' : Set G) := by
  classical
  haveI : CompactSpace Ω := isCompact_iff_compactSpace.1 hΩc
  let H : Subgroup Ω := Ω'.subgroupOf Ω
  have hHo : IsOpen (H : Set Ω) := by
    have : (H : Set Ω) = Subtype.val ⁻¹' (Ω' : Set G) := by
      ext x; simp [H, Subgroup.mem_subgroupOf]
    rw [this]; exact hΩ'o.preimage continuous_subtype_val
  haveI : Finite (Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  haveI : Fintype (Ω ⧸ H) := Fintype.ofFinite _
  let rep : Ω ⧸ H → G := fun q => ((Quotient.out q : Ω) : G)
  have hrepΩ : ∀ q, rep q ∈ Ω := fun q => (Quotient.out q : Ω).2

  have hrep_eq : ∀ q q' : Ω ⧸ H, ∀ u ∈ Ω', ∀ u' ∈ Ω', rep q * u = rep q' * u' → q = q' := by
    intro q q' u hu u' hu' heq
    have h1 : (rep q)⁻¹ * rep q' = u * u'⁻¹ := by
      have : rep q' = rep q * u * u'⁻¹ := by rw [heq, mul_inv_cancel_right]
      rw [this, mul_assoc, inv_mul_cancel_left]
    have hmem : (Quotient.out q : Ω)⁻¹ * (Quotient.out q' : Ω) ∈ H := by
      simp only [H, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      change (rep q)⁻¹ * rep q' ∈ Ω'
      rw [h1]; exact Ω'.mul_mem hu (Ω'.inv_mem hu')
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.2 hmem
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ht
    obtain ⟨q, rfl⟩ := ht
    exact hrepΩ q
  · intro t ht t' ht' hne
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ht ht'
    obtain ⟨q, rfl⟩ := ht
    obtain ⟨q', rfl⟩ := ht'
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', hu'eq⟩ := hx'
    rw [hrep_eq q q' u hu u' hu' hu'eq.symm]
  · ext k
    simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and, exists_prop,
      Set.mem_image]
    constructor
    · intro hk
      let q : Ω ⧸ H := QuotientGroup.mk ⟨k, hk⟩
      have hmem : (Quotient.out q : Ω)⁻¹ * ⟨k, hk⟩ ∈ H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      have hmem' : (rep q)⁻¹ * k ∈ Ω' := by
        simpa [H, Subgroup.mem_subgroupOf] using hmem
      exact ⟨rep q, ⟨q, rfl⟩, (rep q)⁻¹ * k, hmem', by rw [mul_inv_cancel_left]⟩
    · rintro ⟨t, ⟨q, rfl⟩, u, hu, rfl⟩
      exact Ω.mul_mem (hrepΩ q) (hle hu)

theorem setIntegral_translate_eq_card_mul_sum (μ : Measure G) [μ.IsHaarMeasure]
    (Ω Ω' : Subgroup G) (hle : Ω' ≤ Ω)
    (hΩo : IsOpen (Ω : Set G)) (hΩc : IsCompact (Ω : Set G)) (hΩ'o : IsOpen (Ω' : Set G)) :
    ∃ T : Finset G, (↑T ⊆ (Ω : Set G)) ∧ μ (Ω : Set G) = T.card * μ (Ω' : Set G) ∧
      ∀ (v : G → ℂ), (∀ u ∈ Ω', ∀ g : G, v (g * u) = v g) →
        ∀ g : G, ∫ k in (Ω : Set G), v (g * k) ∂μ = (μ (Ω' : Set G)).toReal * ∑ t ∈ T, v (g * t) := by
  obtain ⟨T, hTsub, hdisj, hcover⟩ := exists_finset_coset_decomposition Ω Ω' hle hΩo hΩc hΩ'o

  have hCo : ∀ t : G, IsOpen ((fun x => t * x) '' (Ω' : Set G)) := fun t => (isOpenMap_mul_left t) _ hΩ'o
  have hCm : ∀ t : G, MeasurableSet ((fun x => t * x) '' (Ω' : Set G)) := fun t => (hCo t).measurableSet
  have hμC : ∀ t : G, μ ((fun x => t * x) '' (Ω' : Set G)) = μ (Ω' : Set G) := by
    intro t
    rw [Set.image_mul_left, measure_preimage_mul]
  have hΩ'fin : μ (Ω' : Set G) < ⊤ := (measure_mono hle).trans_lt hΩc.measure_lt_top
  refine ⟨T, hTsub, ?_, ?_⟩
  · conv_lhs => rw [hcover]
    rw [measure_biUnion_finset hdisj (fun t _ => hCm t)]
    simp [hμC, Finset.sum_const, nsmul_eq_mul]
  · intro v hv g
    have hEq : ∀ t : G, Set.EqOn (fun k => v (g * k)) (fun _ => v (g * t)) ((fun x => t * x) '' (Ω' : Set G)) := by
      intro t k hk
      obtain ⟨u, hu, rfl⟩ := hk
      show v (g * (t * u)) = v (g * t)
      rw [← mul_assoc, hv u hu]
    have hInt : ∀ t ∈ T, IntegrableOn (fun k => v (g * k)) ((fun x => t * x) '' (Ω' : Set G)) μ := by
      intro t _
      refine IntegrableOn.congr_fun ?_ (hEq t).symm (hCm t)
      refine integrableOn_const ?_
      rw [hμC]; exact hΩ'fin.ne
    calc ∫ k in (Ω : Set G), v (g * k) ∂μ
        = ∫ k in ⋃ t ∈ T, (fun x => t * x) '' (Ω' : Set G), v (g * k) ∂μ := by rw [← hcover]
      _ = ∑ t ∈ T, ∫ k in (fun x => t * x) '' (Ω' : Set G), v (g * k) ∂μ :=
          integral_biUnion_finset T (fun t _ => hCm t) hdisj hInt
      _ = ∑ t ∈ T, ∫ k in (fun x => t * x) '' (Ω' : Set G), v (g * t) ∂μ := by
          refine Finset.sum_congr rfl fun t _ => setIntegral_congr_fun (hCm t) (hEq t)
      _ = ∑ t ∈ T, (μ (Ω' : Set G)).toReal * v (g * t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [setIntegral_const, measureReal_def, hμC, Complex.real_smul]
      _ = (μ (Ω' : Set G)).toReal * ∑ t ∈ T, v (g * t) := by rw [Finset.mul_sum]

theorem setIntegral_subgroup_mul_left (μ : Measure G) [μ.IsHaarMeasure] (Ω : Subgroup G)
    (hΩm : MeasurableSet (Ω : Set G)) (f : G → ℂ) (k₀ : G) (hk₀ : k₀ ∈ Ω) :
    ∫ k in (Ω : Set G), f (k₀ * k) ∂μ = ∫ k in (Ω : Set G), f k ∂μ := by
  have h1 : (fun k => (Ω : Set G).indicator f (k₀ * k)) = (Ω : Set G).indicator (fun k => f (k₀ * k)) := by
    funext k
    by_cases hk : k ∈ (Ω : Set G)
    · have hk' : k₀ * k ∈ (Ω : Set G) := Ω.mul_mem hk₀ hk
      simp [Set.indicator_of_mem, hk, hk']
    · have hk' : k₀ * k ∉ (Ω : Set G) := fun h =>
        hk (by simpa using Ω.mul_mem (Ω.inv_mem hk₀) h)
      simp [hk, hk']
  rw [← integral_indicator hΩm, ← integral_indicator hΩm, ← h1]
  exact integral_mul_left_eq_self _ k₀

end Haar

end GJA

open GJA in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (ℓ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
        (∀ k ∈ Ω, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓ (fun g => v (g * k)) = ℓ v) →
        ∃ (n : ℕ) (g : Fin n → GL (Fin 2) (p.adicCompletion ℚ)) (a : Fin n → ℂ),
          ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
            ℓ v = ∑ i, a i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), v (g i * k) ∂μ₂ := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ Ω hΩo hΩc ℓ hℓ
  obtain ⟨hKc, hKo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
  have hΩne : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ≠ 0 := hΩo.measure_ne_zero μ₂ ⟨1, Ω.one_mem⟩
  have hΩfin : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ≠ ⊤ := hΩc.measure_lt_top.ne
  have hcΩ : 0 < (μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal := ENNReal.toReal_pos hΩne hΩfin

  let R : GL (Fin 2) (p.adicCompletion ℚ) → ((GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) :=
    fun k => LinearMap.funLeft ℂ ℂ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => x * k)
  let W : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) ⊓ ⨅ k ∈ Ω, LinearMap.ker (R k - LinearMap.id)
  have hWmem : ∀ v, v ∈ W ↔ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) ∧ ∀ k ∈ Ω, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), v (g * k) = v g := by
    intro v
    simp only [W, R, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero, funext_iff, LinearMap.funLeft_apply]
  obtain ⟨B, hB⟩ := hw₂adm Ω hΩo
  have hWle : W ≤ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) := by
    intro v hv
    rw [hWmem] at hv
    exact hB v hv.1 hv.2
  haveI : FiniteDimensional ℂ W := by
    haveI := FiniteDimensional.span_of_finite ℂ (B.finite_toSet)
    exact Submodule.finiteDimensional_of_le hWle
  obtain ⟨T, a, hTa⟩ := exists_finset_apply_eq_sum_eval W ℓ
  refine ⟨T.card, fun i => ((T.equivFin.symm i : T) : GL (Fin 2) (p.adicCompletion ℚ)),
    fun i => ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ * a ((T.equivFin.symm i : T) : GL (Fin 2) (p.adicCompletion ℚ)), ?_⟩
  intro v hv

  obtain ⟨U, hUo, hU⟩ := exists_open_stabilizer_of_mem_span
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKo w₂base hw₂K v hv
  have hΩ'o : IsOpen (((Ω ⊓ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) := by
    rw [Subgroup.coe_inf]; exact hΩo.inter hUo
  obtain ⟨S, hSsub, hμS, hint⟩ :=
    setIntegral_translate_eq_card_mul_sum μ₂ Ω (Ω ⊓ U) inf_le_left hΩo hΩc hΩ'o
  have hint' : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), v (g * k) ∂μ₂ =
      (μ₂ ((Ω ⊓ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal * ∑ t ∈ S, v (g * t) :=
    hint v (fun u hu g => hU u (Subgroup.mem_inf.1 hu).2 g)

  set c₀ : ℂ := ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
    ((μ₂ ((Ω ⊓ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) with hc₀
  set vbar : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
    ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), v (g * k) ∂μ₂ with hvbar
  have hvbar_sum : vbar = ∑ t ∈ S, c₀ • (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * t)) := by
    funext g
    simp only [hvbar, hint', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc₀, Finset.mul_sum, mul_assoc]
  have hvbarV : vbar ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
    rw [hvbar_sum]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (translate_mem_span w₂base v hv t)
  have hvbarΩ : ∀ k ∈ Ω, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), vbar (g * k) = vbar g := by
    intro k hk g
    simp only [hvbar]
    congr 1
    have := setIntegral_subgroup_mul_left μ₂ Ω hΩm (fun x => v (g * x)) k hk
    simpa only [mul_assoc] using this
  have hcard : c₀ * (S.card : ℂ) = 1 := by
    have h1 : (μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal =
        (S.card : ℝ) * (μ₂ ((Ω ⊓ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal := by
      rw [hμS, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hne : ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) ≠ 0 := by exact_mod_cast hcΩ.ne'
    rw [hc₀, mul_assoc, inv_mul_eq_one₀ hne, h1]
    push_cast; ring
  have hℓvbar : ℓ vbar = ℓ v := by
    rw [hvbar_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    have h2 : ∀ t ∈ S, ℓ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * t)) = ℓ v := fun t ht => hℓ t (hSsub ht) v hv
    rw [Finset.sum_congr rfl fun t ht => by rw [h2 t ht], Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      mul_comm (S.card : ℂ), hcard, one_mul]
  have hvbarW : vbar ∈ W := (hWmem vbar).2 ⟨hvbarV, hvbarΩ⟩
  rw [← hℓvbar, hTa vbar hvbarW, ← Finset.sum_coe_sort]
  refine Fintype.sum_equiv T.equivFin _ _ fun x => ?_
  simp only [Equiv.symm_apply_apply, hvbar]
  ring

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible (solution)
