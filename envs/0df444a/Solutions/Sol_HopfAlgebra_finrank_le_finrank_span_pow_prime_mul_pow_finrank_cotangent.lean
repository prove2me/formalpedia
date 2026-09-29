-- Prove2me | solution 1 for HopfAlgebra.finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2a8a4aef-714b-5283-a8ab-0402625fa5f6

import Mathlib
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent

set_option autoImplicit false

universe u v

namespace SemilocalNakayama

open TensorProduct

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

theorem exists_fin_span_eq_top [Finite (MaximalSpectrum R)] [Module.Finite R M] (n : ℕ)
    (rk : ∀ P : MaximalSpectrum R, Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) ≤ n) :
    ∃ b : Fin n → M, Submodule.span R (Set.range b) = ⊤ := by
  classical
  let _ := @Ideal.Quotient.field
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _

  have hI : Pairwise (fun P Q : MaximalSpectrum R => IsCoprime P.1 Q.1) :=
    fun P Q ne => Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)

  have hsp : ∀ P : MaximalSpectrum R, ∃ b' : Fin n → (R ⧸ P.1) ⊗[R] M,
      Submodule.span (R ⧸ P.1) (Set.range b') = ⊤ := by
    intro P
    let e := Module.finBasis (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M)
    refine ⟨fun i => if h : (i : ℕ) < Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) then e ⟨i, h⟩ else 0, ?_⟩
    refine eq_top_iff.mpr (e.span_eq.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 (rk P)⟩, ?_⟩
    simp
  choose b' hb' using hsp

  choose b hb using fun i => Ideal.pi_tensorProductMk_quotient_surjective M (fun P : MaximalSpectrum R => P.1) hI
    (fun P => b' P i)
  refine ⟨b, ?_⟩
  set N : Submodule R M := Submodule.span R (Set.range b) with hN

  let f : M →ₗ[R] (∀ P : MaximalSpectrum R, (R ⧸ P.1) ⊗[R] M) :=
    LinearMap.pi fun P => TensorProduct.mk R (R ⧸ P.1) M 1
  have hfb : ∀ i P, f (b i) P = b' P i := fun i P => by
    have := congrFun (hb i) P
    simpa [f] using this
  have hfN : ∀ m : M, ∃ y ∈ N, f y = f m := by
    intro m

    have hc : ∀ P : MaximalSpectrum R, ∃ c : Fin n → R ⧸ P.1, ∑ i, c i • b' P i = f m P := fun P =>
      (Submodule.mem_span_range_iff_exists_fun (R ⧸ P.1)).mp (by rw [hb' P]; exact Submodule.mem_top)
    choose c hcspec using hc

    have hsurj := Ideal.pi_mkQ_surjective (I := fun P : MaximalSpectrum R => P.1) hI
    choose r hr using fun i => hsurj (fun P => c P i)
    refine ⟨∑ i, r i • b i, Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)), ?_⟩
    funext P
    rw [map_sum, Finset.sum_apply, ← hcspec P]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, hfb, ← algebraMap_smul (R ⧸ P.1) (r i), Ideal.Quotient.algebraMap_eq]
    congr 1
    exact congrFun (hr i) P

  have hker := Ideal.ker_tensorProductMk_quotient M (fun P : MaximalSpectrum R => P.1) hI
  have htop : (⊤ : Submodule R M) ≤ N ⊔ (⨅ P : MaximalSpectrum R, P.1) • ⊤ := by
    intro m _
    obtain ⟨y, hy, hfy⟩ := hfN m
    rw [← hker]
    refine Submodule.mem_sup.mpr ⟨y, hy, m - y, ?_, add_sub_cancel y m⟩
    rw [LinearMap.mem_ker, map_sub, hfy, sub_self]
  have hjac : (⨅ P : MaximalSpectrum R, P.1) ≤ Ideal.jacobson (⊥ : Ideal R) :=
    le_sInf fun J hJ => iInf_le (fun P : MaximalSpectrum R => P.1) ⟨J, hJ.2⟩
  exact top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac htop)

theorem finrank_le_mul_finrank [Finite (MaximalSpectrum R)] (K : Type*) [Field K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K R] [Module.Finite R M] (n : ℕ)
    (rk : ∀ P : MaximalSpectrum R, Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) ≤ n) :
    Module.finrank K M ≤ n * Module.finrank K R := by
  obtain ⟨b, hb⟩ := exists_fin_span_eq_top R M n rk
  let g : (Fin n → R) →ₗ[K] M :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_assoc] }
  have hg : Function.Surjective g := fun m => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (show m ∈ Submodule.span R (Set.range b) by rw [hb]; exact Submodule.mem_top)
    exact ⟨c, hc⟩
  calc Module.finrank K M ≤ Module.finrank K (Fin n → R) := LinearMap.finrank_le_finrank_of_surjective hg
    _ = n * Module.finrank K R := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem span_tmul_eq_top_of_forall_mem_sup (P : Ideal R) (n : ℕ) (s : Fin n → M)
    (hs : ∀ m : M, m ∈ Submodule.span R (Set.range s) ⊔ (P • ⊤ : Submodule R M)) :
    Submodule.span (R ⧸ P) (Set.range fun i => TensorProduct.mk R (R ⧸ P) M 1 (s i)) = ⊤ := by
  classical
  let e := TensorProduct.quotTensorEquivQuotSMul M P
  let φ : M →ₗ[R] (R ⧸ P) ⊗[R] M := TensorProduct.mk R (R ⧸ P) M 1
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective (P • ⊤ : Submodule R M) (e v)
  have hv : v = φ m := by
    rw [← e.symm_apply_apply v, ← hm]; exact TensorProduct.quotTensorEquivQuotSMul_symm_mk P m
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hs m)
  have hz0 : φ z = 0 := by
    show (1 : R ⧸ P) ⊗ₜ[R] z = 0
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk P z, (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  rw [hv, map_add, hz0, add_zero]

  have hy' : φ y ∈ (Submodule.span R (Set.range s)).map φ := Submodule.mem_map_of_mem hy
  rw [Submodule.map_span, ← Set.range_comp] at hy'
  exact Submodule.span_le_restrictScalars R (R ⧸ P) _ hy'

theorem finrank_le_mul_finrank' [Finite (MaximalSpectrum R)] (K : Type*) [Field K] [Algebra K R]
    [Module K M] [IsScalarTower K R M] [Module.Finite K R] [Module.Finite R M] (n : ℕ)
    (rk : ∀ P : MaximalSpectrum R, ∃ s : Fin n → M,
      ∀ m : M, m ∈ Submodule.span R (Set.range s) ⊔ (P.1 • ⊤ : Submodule R M)) :
    Module.finrank K M ≤ n * Module.finrank K R := by
  let _ := @Ideal.Quotient.field
  refine finrank_le_mul_finrank R M K n fun P => ?_
  obtain ⟨s, hs⟩ := rk P
  have h := span_tmul_eq_top_of_forall_mem_sup R M P.1 n s hs
  exact (finrank_le_of_span_eq_top h).trans (by simp)

end SemilocalNakayama

namespace HopfTranslate

open WithConv HopfAlgebra

variable {K : Type*} [CommRing K] {H : Type*} [CommRing H] [HopfAlgebra K H]

noncomputable def invPt (x : H →ₐ[K] K) : H →ₐ[K] K :=
  AlgHom.ofLinearMap (x.toLinearMap ∘ₗ antipode K)
    (by simp [antipode_one])
    (fun a b => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, antipode_mul, map_mul]
      exact mul_comm _ _)

theorem invPt_apply (x : H →ₐ[K] K) (h : H) : invPt x h = x (antipode K h) := rfl

theorem mul_invPt (x : H →ₐ[K] K) : toConv x * toConv (invPt x) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  let ℛ := Coalgebra.Repr.arbitrary K h
  show (toConv x * toConv (invPt x)) h = (1 : WithConv (H →ₐ[K] K)) h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, invPt_apply, ← map_mul, ← map_sum,
    sum_mul_antipode_eq_smul ℛ, map_smul, map_one, smul_eq_mul, mul_one, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem invPt_mul (x : H →ₐ[K] K) : toConv (invPt x) * toConv x = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  let ℛ := Coalgebra.Repr.arbitrary K h
  show (toConv (invPt x) * toConv x) h = (1 : WithConv (H →ₐ[K] K)) h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, invPt_apply, ← map_mul, ← map_sum,
    sum_antipode_mul_eq_smul ℛ, map_smul, map_one, smul_eq_mul, mul_one, Algebra.algebraMap_self,
    RingHom.id_apply]

noncomputable def hat (x : H →ₐ[K] K) : H →ₐ[K] H := (Algebra.ofId K H).comp x

theorem hat_apply (x : H →ₐ[K] K) (h : H) : hat x h = algebraMap K H (x h) := rfl

theorem comp_hat (f : H →ₐ[K] H) (x : H →ₐ[K] K) : f.comp (hat x) = hat x :=
  AlgHom.ext fun h => by rw [AlgHom.comp_apply, hat_apply, AlgHom.commutes]

theorem hat_convMul (x y : H →ₐ[K] K) :
    toConv (hat x) * toConv (hat y) = toConv (hat (toConv x * toConv y).ofConv) := by
  unfold hat
  have h := AlgHom.comp_convMul_distrib (Algebra.ofId K H) (toConv x) (toConv y)
  rw [h, toConv_ofConv]

theorem hat_convOne : hat ((1 : WithConv (H →ₐ[K] K)).ofConv) = (1 : WithConv (H →ₐ[K] H)).ofConv := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv]
  apply AlgHom.ext
  intro h
  rfl

noncomputable def transl (x : H →ₐ[K] K) : H →ₐ[K] H := (toConv (AlgHom.id K H) * toConv (hat x)).ofConv

theorem transl_comp_transl (x y : H →ₐ[K] K) :
    (transl y).comp (transl x) = (toConv (AlgHom.id K H) * toConv (hat (toConv y * toConv x).ofConv)).ofConv := by
  show (transl y).comp ((toConv (AlgHom.id K H) * toConv (hat x)).ofConv) = _
  rw [AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv, AlgHom.comp_id, comp_hat, transl,
    toConv_ofConv, mul_assoc, hat_convMul]

theorem transl_convOne : transl ((1 : WithConv (H →ₐ[K] K)).ofConv) = AlgHom.id K H := by
  rw [transl, hat_convOne, toConv_ofConv, mul_one, ofConv_toConv]

theorem transl_invPt_comp (x : H →ₐ[K] K) : (transl (invPt x)).comp (transl x) = AlgHom.id K H := by
  rw [transl_comp_transl, invPt_mul, hat_convOne, toConv_ofConv, mul_one, ofConv_toConv]

theorem transl_comp_invPt (x : H →ₐ[K] K) : (transl x).comp (transl (invPt x)) = AlgHom.id K H := by
  rw [transl_comp_transl, mul_invPt, hat_convOne, toConv_ofConv, mul_one, ofConv_toConv]

noncomputable def translEquiv (x : H →ₐ[K] K) : H ≃ₐ[K] H :=
  AlgEquiv.ofAlgHom (transl x) (transl (invPt x)) (transl_comp_invPt x) (transl_invPt_comp x)

theorem translEquiv_apply (x : H →ₐ[K] K) (h : H) : translEquiv x h = transl x h := rfl

theorem counit_comp_transl (x : H →ₐ[K] K) : (Bialgebra.counitAlgHom K H).comp (transl x) = x := by
  rw [transl, AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv, AlgHom.comp_id]
  have h1 : toConv (Bialgebra.counitAlgHom K H) = (1 : WithConv (H →ₐ[K] K)) := by
    rw [AlgHom.convOne_def]; rfl
  have h2 : (Bialgebra.counitAlgHom K H).comp (hat x) = x :=
    AlgHom.ext fun h => by rw [AlgHom.comp_apply, hat_apply, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, h2, one_mul, ofConv_toConv]

end HopfTranslate

namespace HopfFibreBound

open HopfTranslate

variable (K : Type*) [Field K] [IsAlgClosed K] (H : Type*) [CommRing H] [HopfAlgebra K H] [Module.Finite K H]

theorem exists_point_of_isMaximal (Q : Ideal H) [hQ : Q.IsMaximal] : ∃ x : H →ₐ[K] K, RingHom.ker x = Q := by
  letI : Field (H ⧸ Q) := Ideal.Quotient.field Q
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ Q)
  let e : K ≃ₐ[K] H ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ Q)) hbij
  refine ⟨(e.symm : H ⧸ Q →ₐ[K] K).comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext h
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  change e.symm (Ideal.Quotient.mk Q h) = 0 ↔ h ∈ Q
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem finrank_le_finrank_quotient_mul (F : Subalgebra K H) (hF : ∀ (φ : H →ₐ[K] H) (a : H), a ∈ F → φ a ∈ F)
    (S : Set H) (hS : S ⊆ F) (hSε : ∀ s ∈ S, Bialgebra.counitAlgHom K H s = 0) :
    Module.finrank K H ≤ Module.finrank K (H ⧸ Ideal.span S) * Module.finrank K F := by
  classical
  haveI : Module.Finite K F := Module.Finite.of_injective F.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing F := IsArtinianRing.of_finite K F
  haveI : Module.Finite F H := Module.Finite.of_restrictScalars_finite K F H
  apply SemilocalNakayama.finrank_le_mul_finrank' F H K
  intro P

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := H) P.1
    (fun f hf => by
      rw [RingHom.mem_ker] at hf
      have : f = 0 := Subtype.ext hf
      rw [this]; exact P.1.zero_mem)
  haveI := hQmax
  obtain ⟨x, hx⟩ := exists_point_of_isMaximal K H Q
  have hPx : ∀ f : F, f ∈ P.1 ↔ x f = 0 := fun f => by
    rw [← hQ, Ideal.mem_comap, ← hx, RingHom.mem_ker]; rfl

  let τ : H ≃ₐ[K] H := translEquiv x
  have hτ : ∀ h, τ h = transl x h := fun h => rfl
  have hετ : ∀ h, Bialgebra.counitAlgHom K H (τ h) = x h := fun h => by
    rw [hτ, ← AlgHom.comp_apply, counit_comp_transl]
  have hετ' : ∀ h, Bialgebra.counitAlgHom K H h = x (τ.symm h) := fun h => by
    conv_lhs => rw [← τ.apply_symm_apply h]
    exact hετ _
  have hτF : ∀ a ∈ F, τ a ∈ F := fun a ha => hF (transl x) a ha
  have hτF' : ∀ a ∈ F, τ.symm a ∈ F := fun a ha => hF (transl (invPt x)) a ha

  let IP : Ideal H := P.1.map (algebraMap F H)
  let Pe : Ideal F := (RingHom.ker (Bialgebra.counitAlgHom K H)).comap (algebraMap F H)
  let Ie : Ideal H := Pe.map (algebraMap F H)
  have hIe : Ie = IP.map (τ : H →+* H) := by
    apply le_antisymm
    ·
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap] at hg
      rw [Ideal.mem_comap]
      have h1 : (algebraMap F H g) = τ (τ.symm g) := (τ.apply_symm_apply _).symm
      rw [h1]
      apply Ideal.mem_map_of_mem
      have hmem : τ.symm (g : H) ∈ F := hτF' g g.2
      have : (⟨τ.symm (g : H), hmem⟩ : F) ∈ P.1 := by
        rw [hPx, ← hετ']; exact hg
      exact Ideal.mem_map_of_mem (algebraMap F H) this
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      have hmem : τ (f : H) ∈ F := hτF f f.2
      have : (⟨τ (f : H), hmem⟩ : F) ∈ Pe := by
        show algebraMap F H ⟨τ (f : H), hmem⟩ ∈ RingHom.ker (Bialgebra.counitAlgHom K H)
        rw [RingHom.mem_ker]
        show Bialgebra.counitAlgHom K H (τ f) = 0
        rw [hετ]; exact (hPx f).mp hf
      exact Ideal.mem_map_of_mem (algebraMap F H) this

  have hdimPe : Module.finrank K (H ⧸ IP) = Module.finrank K (H ⧸ Ie) :=
    (Ideal.quotientEquivAlg IP Ie τ hIe).toLinearEquiv.finrank_eq

  have hSIe : Ideal.span S ≤ Ie := by
    rw [Ideal.span_le]
    intro s hs
    have : (⟨s, hS hs⟩ : F) ∈ Pe := by
      show algebraMap F H ⟨s, hS hs⟩ ∈ RingHom.ker (Bialgebra.counitAlgHom K H)
      rw [RingHom.mem_ker]; exact hSε s hs
    exact Ideal.mem_map_of_mem (algebraMap F H) this
  have hdimS : Module.finrank K (H ⧸ Ie) ≤ Module.finrank K (H ⧸ Ideal.span S) :=
    LinearMap.finrank_le_finrank_of_surjective (f := (Ideal.Quotient.factorₐ K hSIe).toLinearMap)
      (Ideal.Quotient.factor_surjective hSIe)

  set n := Module.finrank K (H ⧸ Ideal.span S) with hn
  have hdim : Module.finrank K (H ⧸ IP) ≤ n := hdimPe ▸ hdimS
  let bV := Module.finBasis K (H ⧸ IP)
  let t : Fin n → H ⧸ IP := fun i => if h : (i : ℕ) < Module.finrank K (H ⧸ IP) then bV ⟨i, h⟩ else 0
  have ht : Submodule.span K (Set.range t) = ⊤ := by
    refine eq_top_iff.mpr (bV.span_eq.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨j, lt_of_lt_of_le j.2 hdim⟩, ?_⟩
    simp [t]
  choose s hs using fun i => Ideal.Quotient.mk_surjective (t i)
  refine ⟨s, fun m => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (show Ideal.Quotient.mk IP m ∈ Submodule.span K (Set.range t) by rw [ht]; exact Submodule.mem_top)
  have hdiff : m - ∑ i, c i • s i ∈ IP := by
    rw [← Ideal.Quotient.eq, map_sum]
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hs i, ← Ideal.Quotient.mkₐ_eq_mk K, map_smul]
  refine Submodule.mem_sup.mpr ⟨∑ i, c i • s i, ?_, m - ∑ i, c i • s i, ?_, add_sub_cancel _ _⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F (c i) (s i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Ideal.smul_top_eq_map]
    exact hdiff

end HopfFibreBound

namespace HopfFibreBound

theorem adjoin_pow_stable (K : Type*) [Field K] (H : Type*) [CommRing H] [Algebra K H] (p : ℕ)
    (φ : H →ₐ[K] H) (a : H) (ha : a ∈ Algebra.adjoin K (Set.range fun b : H => b ^ p)) :
    φ a ∈ Algebra.adjoin K (Set.range fun b : H => b ^ p) := by
  have h1 : φ a ∈ (Algebra.adjoin K (Set.range fun b : H => b ^ p)).map φ := Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
  rw [AlgHom.map_adjoin] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  exact ⟨φ b, by rw [map_pow]⟩

theorem finrank_le_finrank_adjoin_pow_mul (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Type*) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K H ≤
      Module.finrank K ↥(Algebra.adjoin K (Set.range fun a : H => a ^ p)) *
        p ^ Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent := by
  rw [← HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent K p H, mul_comm]
  refine finrank_le_finrank_quotient_mul K H (Algebra.adjoin K (Set.range fun a : H => a ^ p))
    (adjoin_pow_stable K H p) _ ?_ ?_
  · rintro _ ⟨a, _, rfl⟩
    exact Algebra.subset_adjoin ⟨a, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [map_pow, show Bialgebra.counitAlgHom K H a = 0 from ha, zero_pow (Fact.out : p.Prime).ne_zero]

end HopfFibreBound

theorem HopfFibreBound.adjoin_pow_toSubmodule (K : Type*) [Field K] (H : Type*) [CommRing H] [Algebra K H] (p : ℕ) :
    (Algebra.adjoin K (Set.range fun a : H => a ^ p)).toSubmodule = Submodule.span K (Set.range fun a : H => a ^ p) := by
  rw [Algebra.adjoin_eq_span]
  congr 1
  have : (Set.range fun a : H => a ^ p) = (MonoidHom.mrange (powMonoidHom p : H →* H) : Set H) := by
    ext x
    simp only [Set.mem_range, SetLike.mem_coe, MonoidHom.mem_mrange, powMonoidHom_apply]
  rw [this, Submonoid.closure_eq]

open HopfFibreBound in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K H ≤
      Module.finrank K ↥(Submodule.span K (Set.range fun a : H => a ^ p)) *
        p ^ Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent := by
  have hfin : Module.finrank K ↥(Submodule.span K (Set.range fun a : H => a ^ p)) =
      Module.finrank K ↥(Algebra.adjoin K (Set.range fun a : H => a ^ p)) := by
    rw [← (LinearEquiv.ofEq _ _ (adjoin_pow_toSubmodule K H p)).finrank_eq]
    exact Subalgebra.finrank_toSubmodule _
  rw [hfin]
  exact finrank_le_finrank_adjoin_pow_mul K p H

end S_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent
end P2MW
export P2MW.S_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent (solution)
