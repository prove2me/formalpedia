-- Prove2me | solution 1 for IsDiscreteValuationRing.charpoly_mulLeft_quotient_eq_finprod_single_slope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c19f1e72-1e41-5d2c-ac86-02e1e861cdc6

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope

set_option maxHeartbeats 800000
set_option autoImplicit false

universe u v w

namespace P1Arch

theorem moduleFinite_localization_atPrime_of_moduleFinite
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (m : MaximalSpectrum A) :
    Module.Finite K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)

theorem finrank_eq_sum_finrank_localization_atPrime
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [Fintype (MaximalSpectrum A)] :
    Module.finrank K A = ∑ m : MaximalSpectrum A, Module.finrank K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : ∀ m : MaximalSpectrum A, Module.Finite K (Localization.AtPrime m.asIdeal) :=
    fun m => moduleFinite_localization_atPrime_of_moduleFinite K A m
  let e : A ≃ₗ[K] MaximalSpectrum.PiLocalization A :=
    (MaximalSpectrum.toPiLocalizationEquiv A).toLinearEquiv.restrictScalars K
  rw [e.finrank_eq]
  exact Module.finrank_pi_fintype K

end P1Arch

namespace P1Arch

open IsLocalRing

theorem finrank_eq_finrank_residueField_mul_length
    (K : Type u) (L : Type v) (M : Type w) [Field K] [CommRing L] [IsLocalRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite K M] :
    (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M := by

  suffices h : ∀ n : ℕ, ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
      [Module.Finite K M], Module.finrank K M = n →
      (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  by_cases hM : Subsingleton M
  · rw [Module.finrank_zero_of_subsingleton, Module.length_eq_zero_iff.mpr hM, Nat.cast_zero, mul_zero]
  · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM

    haveI : IsArtinian L M := isArtinian_of_tower K inferInstance
    haveI : IsNoetherian L M := isNoetherian_of_tower K inferInstance
    obtain ⟨S, hS⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule L M)).resolve_left top_ne_bot
    obtain ⟨hSatom, -⟩ := hS
    haveI hSsimple : IsSimpleModule L S := isSimpleModule_iff_isAtom.mpr hSatom

    obtain ⟨I, hImax, ⟨eS⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSsimple
    have hI : I = maximalIdeal L := IsLocalRing.eq_maximalIdeal hImax
    subst hI
    have hfinS : Module.finrank K S = Module.finrank K (IsLocalRing.ResidueField L) :=
      (eS.restrictScalars K).finrank_eq

    haveI : Module.Finite K (M ⧸ S) :=
      Module.Finite.of_surjective (S.mkQ.restrictScalars K) (Submodule.mkQ_surjective S)
    have hdim : Module.finrank K M = Module.finrank K S + Module.finrank K (M ⧸ S) := by
      rw [← (Submodule.Quotient.restrictScalarsEquiv K S).finrank_eq, add_comm]
      exact (Submodule.finrank_quotient_add_finrank (S.restrictScalars K)).symm
    have hκpos : 0 < Module.finrank K (IsLocalRing.ResidueField L) := by
      rw [← hfinS]
      haveI : Nontrivial S := IsSimpleModule.nontrivial L S
      haveI : Module.Finite K S := Module.Finite.of_injective (S.subtype.restrictScalars K) (Submodule.injective_subtype S)
      exact Module.finrank_pos
    have hlt : Module.finrank K (M ⧸ S) < n := by omega
    have ihq := ih _ hlt (M ⧸ S) rfl

    have hlen : Module.length L M = 1 + Module.length L (M ⧸ S) := by
      rw [Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
        (LinearMap.exact_subtype_mkQ S), Module.length_eq_one_iff.mpr hSsimple]
    rw [hdim, hfinS, Nat.cast_add, ihq, hlen, mul_add, mul_one]

end P1Arch

open IsLocalRing
open scoped TensorProduct

namespace P1Arch

theorem length_eq_of_orderIso {R : Type*} {R' : Type*} [Ring R] [Ring R'] {M : Type*} {M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (e : Submodule R M ≃o Submodule R' M') :
    Module.length R M = Module.length R' M' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e

theorem length_self_eq_of_ringEquiv {R : Type*} {R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' :=
  (length_eq_of_orderIso (Ideal.relIsoOfBijective e e.bijective)).symm

noncomputable def restrictScalarsOrderIsoOfSurjective (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Submodule T N ≃o Submodule S N where
  toFun p := p.restrictScalars S
  invFun p :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t n hn => by
        obtain ⟨s, rfl⟩ := h t
        rw [algebraMap_smul]
        exact p.smul_mem s hn }
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl
  map_rel_iff' := Iff.rfl

theorem length_eq_of_surjective_algebraMap (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Module.length S N = Module.length T N :=
  (length_eq_of_orderIso (restrictScalarsOrderIsoOfSurjective S T N h)).symm

theorem length_localization_atPrime_eq_of_isLocalization
    (B : Type u) [CommRing B] (S : Submonoid B) (A : Type v) [CommRing A] [Algebra B A] [IsLocalization S A]
    (𝔪 : Ideal A) [𝔪.IsPrime] :
    Module.length (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪) =
      Module.length (Localization.AtPrime (𝔪.comap (algebraMap B A))) (Localization.AtPrime (𝔪.comap (algebraMap B A))) := by
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔪) (𝔪.comap (algebraMap B A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (Localization.AtPrime 𝔪) 𝔪
  exact length_self_eq_of_ringEquiv
    (IsLocalization.algEquiv (𝔪.comap (algebraMap B A)).primeCompl (Localization.AtPrime 𝔪)
      (Localization.AtPrime (𝔪.comap (algebraMap B A)))).toRingEquiv

theorem length_localizedModule_quotient_eq_length_localization
    (R : Type u) [CommRing R] (I : Ideal R) (Q : Ideal (R ⧸ I)) [Q.IsPrime] :
    Module.length (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
        (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) := by
  set P : Ideal R := Q.comap (Ideal.Quotient.mk I) with hP

  have hS : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = Q.primeCompl := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hz
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨s, hz, rfl⟩

  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) (Localization.AtPrime Q) := by
    rw [hS]; infer_instance
  haveI hloc : IsLocalizedModule P.primeCompl
      (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  let e₀ : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[R] Localization.AtPrime Q :=
    IsLocalizedModule.iso P.primeCompl (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap

  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Ideal.Quotient.mk I) hP
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      change algebraMap (R ⧸ I) (Localization.AtPrime Q) (Ideal.Quotient.mk I r) = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map])
  have hφ : Function.Surjective (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    intro z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ I)
    have hs'P : s' ∈ P.primeCompl := by
      change Ideal.Quotient.mk I s' ∉ Q
      rw [hs']; exact s.2
    refine ⟨IsLocalization.mk' _ a' ⟨s', hs'P⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_mk']
    congr 1
    · exact Subtype.ext hs'
  let e : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[Localization.AtPrime P] Localization.AtPrime Q :=
    LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P) e₀
  rw [e.length_eq]
  exact length_eq_of_surjective_algebraMap _ _ _ hφ

end P1Arch

open IsLocalRing
open scoped TensorProduct

namespace P1Arch

theorem finrank_residueField_localization_eq_finrank_quotient_aux
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    Module.finrank K (ResidueField (Localization.AtPrime 𝔪)) = Module.finrank K (A ⧸ 𝔪) := by
  let ρ : A →+* ResidueField (Localization.AtPrime 𝔪) :=
    (residue (Localization.AtPrime 𝔪)).comp (algebraMap A (Localization.AtPrime 𝔪))
  have hρ : ∀ a ∈ 𝔪, ρ a = 0 := by
    intro a ha
    change residue _ (algebraMap A (Localization.AtPrime 𝔪) a) = 0
    rw [residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mpr ha
  let ψ₀ : (A ⧸ 𝔪) →+* ResidueField (Localization.AtPrime 𝔪) := Ideal.Quotient.lift 𝔪 ρ hρ
  have hψmk : ∀ a : A, ψ₀ (Ideal.Quotient.mk _ a) = residue _ (algebraMap A (Localization.AtPrime 𝔪) a) :=
    fun a => rfl
  have hKL : ∀ k : K, algebraMap K (ResidueField (Localization.AtPrime 𝔪)) k =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) (algebraMap K A k)) := by
    intro k
    rw [← IsScalarTower.algebraMap_apply K A (Localization.AtPrime 𝔪) k,
      IsScalarTower.algebraMap_apply K (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) k,
      ResidueField.algebraMap_eq]
  let ψ : (A ⧸ 𝔪) →ₗ[K] ResidueField (Localization.AtPrime 𝔪) :=
    { toFun := ψ₀
      map_add' := ψ₀.map_add
      map_smul' := by
        intro k x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, hKL, ← hψmk, ← map_mul, IsScalarTower.algebraMap_apply K A (A ⧸ 𝔪) k,
          Ideal.Quotient.algebraMap_eq, ← map_mul] }
  have hψapply : ∀ x, ψ x = ψ₀ x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hψapply, hψmk, residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl l
    have hs0 : (Ideal.Quotient.mk 𝔪 (s : A)) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact s.2
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ t', ?_⟩
    have hsunit : residue _ (algebraMap A (Localization.AtPrime 𝔪) s) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪]
      exact s.2
    apply mul_right_cancel₀ hsunit
    dsimp only
    rw [hψapply]
    change ψ₀ _ * _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔪) a s) *
      residue _ (algebraMap A (Localization.AtPrime 𝔪) s)
    have hts : Ideal.Quotient.mk 𝔪 t' * Ideal.Quotient.mk 𝔪 (s : A) = 1 := by
      rw [mul_comm]; exact ht
    rw [← map_mul (residue _), IsLocalization.mk'_spec, ← hψmk a, ← hψmk (s : A), ← map_mul ψ₀, mul_assoc,
      hts, mul_one]
  exact ((LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).finrank_eq).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem finrank_quotient_tensor_eq_finrank_quotient
    (W : Type u) [CommRing W] [IsDomain W] (B : Type u) [CommRing B] [Algebra W B]
    (𝔪 : Ideal ((FractionRing W) ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B ((FractionRing W) ⊗[W] B)))] :
    Module.finrank (FractionRing W) (((FractionRing W) ⊗[W] B) ⧸ 𝔪) =
      Module.finrank W (B ⧸ 𝔪.comap (algebraMap B ((FractionRing W) ⊗[W] B))) := by
  set Q : Ideal B := 𝔪.comap (algebraMap B (FractionRing W ⊗[W] B)) with hQ
  have halg : ∀ b : B, algebraMap B (FractionRing W ⊗[W] B) b = (1 : FractionRing W) ⊗ₜ[W] b := fun b => rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (FractionRing W ⊗[W] B) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  have h𝔪 : 𝔪 = Q.map (algebraMap B (FractionRing W ⊗[W] B)) :=
    (IsLocalization.map_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (FractionRing W ⊗[W] B) 𝔪).symm
  let Q' : Submodule W B := Q.restrictScalars W
  let f : (FractionRing W) ⊗[W] Q' →ₗ[FractionRing W] (FractionRing W ⊗[W] B) := (Q'.subtype).baseChange (FractionRing W)
  let g : (FractionRing W ⊗[W] B) →ₗ[FractionRing W] (FractionRing W) ⊗[W] (B ⧸ Q') := (Q'.mkQ).baseChange (FractionRing W)
  have hftmul : ∀ (k : FractionRing W) (q : Q'), f (k ⊗ₜ q) = k ⊗ₜ (q : B) := fun k q => by
    simp only [f, LinearMap.baseChange_tmul, Submodule.subtype_apply]
  have hgsurj : Function.Surjective g := by
    change Function.Surjective ((Q'.mkQ).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective Q')
  have hexact : Function.Exact f g := by
    change Function.Exact ((Q'.subtype).baseChange (FractionRing W)) ((Q'.mkQ).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (FractionRing W) (LinearMap.exact_subtype_mkQ Q') (Submodule.mkQ_surjective Q')
  have hrange : LinearMap.range f = 𝔪.restrictScalars (FractionRing W) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul k q =>
        rw [hftmul, Submodule.restrictScalars_mem]
        have : (k ⊗ₜ[W] (q : B) : FractionRing W ⊗[W] B) =
            (k ⊗ₜ[W] (1 : B)) * algebraMap B (FractionRing W ⊗[W] B) q := by
          rw [halg, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        exact 𝔪.mul_mem_left _ (Ideal.mem_comap.mp q.2)
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro x hx
      rw [Submodule.restrictScalars_mem, h𝔪] at hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨q, hq, rfl⟩
        exact ⟨1 ⊗ₜ ⟨q, hq⟩, by rw [hftmul, halg]⟩
      · exact Submodule.zero_mem _
      · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
      · intro a y hymem hy
        obtain ⟨z, rfl⟩ := hy
        clear hymem
        rw [smul_eq_mul]
        induction a using TensorProduct.induction_on with
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | tmul k b =>
          induction z using TensorProduct.induction_on with
          | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
          | tmul k' q =>
            refine ⟨(k * k') ⊗ₜ ⟨b * q, Q.mul_mem_left b q.2⟩, ?_⟩
            rw [hftmul, hftmul, Algebra.TensorProduct.tmul_mul_tmul]
          | add z₁ z₂ h₁ h₂ => rw [map_add, mul_add]; exact Submodule.add_mem _ h₁ h₂
        | add a₁ a₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  let e₁ : ((FractionRing W ⊗[W] B) ⧸ 𝔪) ≃ₗ[FractionRing W] ((FractionRing W ⊗[W] B) ⧸ 𝔪.restrictScalars (FractionRing W)) :=
    (Submodule.Quotient.restrictScalarsEquiv (FractionRing W) 𝔪).symm
  let e₂ : ((FractionRing W ⊗[W] B) ⧸ 𝔪.restrictScalars (FractionRing W)) ≃ₗ[FractionRing W]
      ((FractionRing W ⊗[W] B) ⧸ LinearMap.ker g) :=
    Submodule.quotEquivOfEq _ _ (by rw [← hrange, hexact.linearMap_ker_eq])
  let e₃ : ((FractionRing W ⊗[W] B) ⧸ LinearMap.ker g) ≃ₗ[FractionRing W] (FractionRing W) ⊗[W] (B ⧸ Q') :=
    g.quotKerEquivOfSurjective hgsurj
  let e₄ : (B ⧸ Q') ≃ₗ[W] (B ⧸ Q) := Submodule.Quotient.restrictScalarsEquiv W Q
  haveI : Module.Free W (B ⧸ Q') := Module.Free.of_equiv e₄.symm
  rw [(e₁.trans (e₂.trans e₃)).finrank_eq, Module.finrank_baseChange, e₄.finrank_eq]

theorem finrank_residueField_localization_eq_finrank_quotient
    (W : Type u) [CommRing W] [IsDomain W] (B : Type u) [CommRing B] [Algebra W B]
    [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] B)]
    (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] B))
    [Module.Free W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B)))] :
    Module.finrank (FractionRing W) (ResidueField (Localization.AtPrime 𝔪.asIdeal)) =
      Module.finrank W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B))) := by
  haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  rw [finrank_residueField_localization_eq_finrank_quotient_aux (FractionRing W) _ 𝔪.asIdeal]
  exact finrank_quotient_tensor_eq_finrank_quotient W B 𝔪.asIdeal

end P1Arch

namespace P1Arch
open IsLocalRing
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section GenericH1
variable {W : Type u} [CommRing W] [IsDomain W]
variable (R : Type u) [CommRing R] [Algebra W R] (I : Ideal R)

noncomputable def primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) : PrimeSpectrum R :=
  ⟨(𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I), by
    haveI := 𝔪.isMaximal.isPrime
    exact inferInstance⟩

theorem primeOfMax_asIdeal (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    (primeOfMax R I 𝔪).asIdeal =
      (𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I) := rfl

theorem primeOfMax_injective : Function.Injective (primeOfMax (W := W) R I) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  intro 𝔪₁ 𝔪₂ h
  have h1 := congrArg (fun P : PrimeSpectrum R => (P.asIdeal.map (Ideal.Quotient.mk I)).map
    (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) h
  simp only [primeOfMax_asIdeal, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))] at h1
  cases 𝔪₁; cases 𝔪₂; simp only at h1; subst h1; rfl

theorem le_primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) : I ≤ (primeOfMax R I 𝔪).asIdeal := by
  intro y hy
  rw [primeOfMax_asIdeal, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  exact Ideal.zero_mem _

theorem disjoint_primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑(primeOfMax R I 𝔪).asIdeal := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  rw [Set.disjoint_left]
  intro r hr hrP
  obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hr
  rw [SetLike.mem_coe, primeOfMax_asIdeal, Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.mk_algebraMap] at hrP
  have hu : IsUnit (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)) (algebraMap W (R ⧸ I) w)) :=
    IsLocalization.map_units ((FractionRing W) ⊗[W] (R ⧸ I))
      ⟨algebraMap W (R ⧸ I) w, Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩⟩
  exact 𝔪.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hrP hu)

theorem mem_range_primeOfMax [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (P : PrimeSpectrum R) (hIP : I ≤ P.asIdeal)
    (hdisj : Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal) :
    P ∈ Set.range (primeOfMax (W := W) R I) := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI : IsArtinianRing ((FractionRing W) ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite (FractionRing W) _
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P.asIdeal := by rw [Ideal.mk_ker]; exact hIP
  haveI hPbar : (P.asIdeal.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hback : (P.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hdisj' : Disjoint (↑(Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) : Set (R ⧸ I))
      ↑(P.asIdeal.map (Ideal.Quotient.mk I)) := by
    rw [Set.disjoint_left]
    intro b hb hbP
    obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hb
    rw [SetLike.mem_coe, ← Ideal.Quotient.mk_algebraMap, ← Ideal.mem_comap, hback] at hbP
    exact Set.disjoint_left.mp hdisj (Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩) hbP
  set 𝔪 : Ideal ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    (P.asIdeal.map (Ideal.Quotient.mk I)).map (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I))) with h𝔪
  haveI h𝔪p : 𝔪.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPbar hdisj'
  haveI h𝔪m : 𝔪.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔪
  refine ⟨⟨𝔪, h𝔪m⟩, ?_⟩
  ext1
  rw [primeOfMax_asIdeal]
  change (Ideal.comap (algebraMap (R ⧸ I) _) 𝔪).comap _ = _
  have hunder : Ideal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I))) 𝔪 = P.asIdeal.map (Ideal.Quotient.mk I) :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) _ hPbar hdisj'
  rw [hunder, hback]

noncomputable def quotQuotEquiv (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) ≃ₗ[W]
      R ⧸ (primeOfMax R I 𝔪).asIdeal := by
  refine ((Ideal.quotientEquivAlgOfEq W ?_).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ W (le_primeOfMax R I 𝔪))).toLinearEquiv

  rw [primeOfMax_asIdeal]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ W I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) =
      Ideal.map (Ideal.Quotient.mk I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem finrank_localization_atPrime_eq [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I)))
    (hfin : Module.Finite W (R ⧸ (primeOfMax R I 𝔪).asIdeal)) (hfree : Module.Free W (R ⧸ (primeOfMax R I 𝔪).asIdeal)) :
    (Module.finrank (FractionRing W) (Localization.AtPrime 𝔪.asIdeal) : ℕ∞) =
      (Module.finrank W (R ⧸ (primeOfMax R I 𝔪).asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime (primeOfMax R I 𝔪).asIdeal)
          (LocalizedModule (primeOfMax R I 𝔪).asIdeal.primeCompl (R ⧸ I)) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI := 𝔪.isMaximal.isPrime
  haveI : Module.Finite (FractionRing W) (Localization.AtPrime 𝔪.asIdeal) :=
    moduleFinite_localization_atPrime_of_moduleFinite (FractionRing W) _ 𝔪
  haveI : Module.Finite W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) :=
    Module.Finite.equiv (quotQuotEquiv R I 𝔪).symm
  haveI : Module.Free W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) :=
    Module.Free.of_equiv (quotQuotEquiv R I 𝔪).symm
  rw [finrank_eq_finrank_residueField_mul_length (FractionRing W) (Localization.AtPrime 𝔪.asIdeal)
      (Localization.AtPrime 𝔪.asIdeal),
    finrank_residueField_localization_eq_finrank_quotient W (R ⧸ I) 𝔪,
    (quotQuotEquiv R I 𝔪).finrank_eq,
    length_localization_atPrime_eq_of_isLocalization (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))
      ((FractionRing W) ⊗[W] (R ⧸ I)) 𝔪.asIdeal]
  congr 1
  exact (length_localizedModule_quotient_eq_length_localization R I _).symm

theorem finrank_tensor_quotient_eq_finsum_generic [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (hff : ∀ P : PrimeSpectrum R, I ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    (Module.finrank (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I)) : ℕ∞) =
      ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
          Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
        (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ I)) := by
  classical
  haveI : IsArtinianRing ((FractionRing W) ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite (FractionRing W) _
  haveI : Finite (MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) := IsArtinianRing.instFiniteMaximalSpectrum _
  letI : Fintype (MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) := Fintype.ofFinite _
  have hrange : Set.range (primeOfMax (W := W) R I) = {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal} := by
    ext P
    constructor
    · rintro ⟨𝔪, rfl⟩
      exact ⟨le_primeOfMax R I 𝔪, disjoint_primeOfMax R I 𝔪⟩
    · rintro ⟨h1, h2⟩
      exact mem_range_primeOfMax R I P h1 h2
  rw [← hrange, finsum_mem_range (primeOfMax_injective R I), finsum_eq_sum_of_fintype,
    finrank_eq_sum_finrank_localization_atPrime (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I)), Nat.cast_sum]
  refine Finset.sum_congr rfl fun 𝔪 _ => ?_
  obtain ⟨hfin, hfree⟩ := hff (primeOfMax R I 𝔪) (le_primeOfMax R I 𝔪) (disjoint_primeOfMax R I 𝔪)
  exact finrank_localization_atPrime_eq R I 𝔪 hfin hfree

end GenericH1
end P1Arch

open IsLocalRing Polynomial

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

def IsPureSlope (r : ℕ) (n : W) (d : ℕ) (f : Polynomial W) : Prop :=
  f.Monic ∧ f.natDegree = d ∧
    (∀ i : ℕ, i ≤ d → ((d - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W n ≤
      (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff i)) ∧
    ((d : ℕ∞) * IsDiscreteValuationRing.addVal W n = (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff 0))

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

theorem IsPureSlope.le_all {r : ℕ} {n : W} {d : ℕ} {f : Polynomial W} (hf : IsPureSlope r n d f) (i : ℕ) :
    ((d - i : ℕ) : ℕ∞) * addv n ≤ (r : ℕ∞) * addv (f.coeff i) := by
  by_cases hi : i ≤ d
  · exact hf.2.2.1 i hi
  · have : d - i = 0 := by omega
    rw [this, Nat.cast_zero, zero_mul]
    exact bot_le

omit [IsDiscreteValuationRing W] in

theorem le_mul_addVal_sum [IsDiscreteValuationRing W] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (t : ι → W)
    (r : ℕ) (C : ℕ∞) (h : ∀ a ∈ s, C ≤ (r : ℕ∞) * addv (t a)) : C ≤ (r : ℕ∞) * addv (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (Finset.not_nonempty_empty)
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    by_cases hs' : s.Nonempty
    · have h1 : C ≤ (r : ℕ∞) * addv (t a) := h a (Finset.mem_insert_self a s)
      have h2 : C ≤ (r : ℕ∞) * addv (∑ x ∈ s, t x) := ih hs' (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hmin : min (addv (t a)) (addv (∑ x ∈ s, t x)) ≤ addv (t a + ∑ x ∈ s, t x) :=
        (IsDiscreteValuationRing.addVal W).map_add _ _
      calc C ≤ (r : ℕ∞) * min (addv (t a)) (addv (∑ x ∈ s, t x)) := by
              rw [mul_min]; exact le_min h1 h2
        _ ≤ (r : ℕ∞) * addv (t a + ∑ x ∈ s, t x) := mul_le_mul_right hmin _
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs', Finset.sum_empty, add_zero]
      exact h a (Finset.mem_insert_self a s)

theorem IsPureSlope.mul {r : ℕ} {n : W} {d d' : ℕ} {f g : Polynomial W}
    (hf : IsPureSlope r n d f) (hg : IsPureSlope r n d' g) : IsPureSlope r n (d + d') (f * g) := by
  have hfa := hf.le_all
  have hga := hg.le_all
  obtain ⟨hfm, hfd, hfi, hf0⟩ := hf
  obtain ⟨hgm, hgd, hgi, hg0⟩ := hg
  refine ⟨hfm.mul hgm, by rw [hfm.natDegree_mul hgm, hfd, hgd], ?_, ?_⟩
  · intro k _
    rw [Polynomial.coeff_mul]
    refine le_mul_addVal_sum _ ⟨(0, k), by simp⟩ _ r _ ?_
    rintro ⟨i, j⟩ hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [IsDiscreteValuationRing.addVal_mul, mul_add]
    calc ((d + d' - k : ℕ) : ℕ∞) * addv n
        ≤ (((d - i : ℕ) : ℕ∞) + ((d' - j : ℕ) : ℕ∞)) * addv n := by
          rw [← Nat.cast_add]
          exact mul_le_mul_left (by exact_mod_cast (show d + d' - k ≤ (d - i) + (d' - j) by omega)) _
      _ = ((d - i : ℕ) : ℕ∞) * addv n + ((d' - j : ℕ) : ℕ∞) * addv n := add_mul _ _ _
      _ ≤ (r : ℕ∞) * addv (f.coeff i) + (r : ℕ∞) * addv (g.coeff j) := add_le_add (hfa i) (hga j)
  · rw [Polynomial.mul_coeff_zero, IsDiscreteValuationRing.addVal_mul, mul_add, ← hf0, ← hg0, ← add_mul,
      ← Nat.cast_add]

theorem isPureSlope_one (r : ℕ) (n : W) : IsPureSlope r n 0 (1 : Polynomial W) := by
  refine ⟨Polynomial.monic_one, Polynomial.natDegree_one, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst this
    simp
  · simp

theorem IsPureSlope.pow {r : ℕ} {n : W} {d : ℕ} {f : Polynomial W} (hf : IsPureSlope r n d f) (ℓ : ℕ) :
    IsPureSlope r n (d * ℓ) (f ^ ℓ) := by
  induction ℓ with
  | zero => rw [mul_zero, pow_zero]; exact isPureSlope_one r n
  | succ ℓ ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hf

theorem IsPureSlope.prod {r : ℕ} {n : W} {ι : Type*} (s : Finset ι) (d : ι → ℕ) (f : ι → Polynomial W)
    (h : ∀ i ∈ s, IsPureSlope r n (d i) (f i)) : IsPureSlope r n (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isPureSlope_one r n
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    exact (h a (Finset.mem_insert_self a s)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end P1Arch

open Polynomial

namespace P1Arch

theorem toMatrix_prod_eq_fromBlocks {K : Type u} [CommRing K] {N P : Type v} [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] {ιN ιP : Type*} [Fintype ιN] [Fintype ιP] [DecidableEq ιN] [DecidableEq ιP]
    (bN : Module.Basis ιN K N) (bP : Module.Basis ιP K P) (f : (N × P) →ₗ[K] (N × P)) :
    LinearMap.toMatrix (bN.prod bP) (bN.prod bP) f =
      Matrix.fromBlocks
        (LinearMap.toMatrix bN bN ((LinearMap.fst K N P).comp (f.comp (LinearMap.inl K N P))))
        (LinearMap.toMatrix bP bN ((LinearMap.fst K N P).comp (f.comp (LinearMap.inr K N P))))
        (LinearMap.toMatrix bN bP ((LinearMap.snd K N P).comp (f.comp (LinearMap.inl K N P))))
        (LinearMap.toMatrix bP bP ((LinearMap.snd K N P).comp (f.comp (LinearMap.inr K N P)))) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply, Matrix.fromBlocks, Module.Basis.prod_apply, Module.Basis.prod_repr_inl,
      Module.Basis.prod_repr_inr]

theorem charpoly_eq_charpoly_restrict_mul_charpoly_quotient
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : V →ₗ[K] V) (N : Submodule K V) (hN : N ≤ N.comap T) :
    T.charpoly = (T.restrict (p := N) (q := N) (fun x hx => hN hx)).charpoly * (N.mapQ N T hN).charpoly := by
  classical
  obtain ⟨P, hNP⟩ := N.exists_isCompl

  let e : V ≃ₗ[K] (N × P) := (Submodule.prodEquivOfIsCompl N P hNP).symm
  let T' : (N × P) →ₗ[K] (N × P) := e.conj T
  have hT' : T'.charpoly = T.charpoly := LinearEquiv.charpoly_conj e T
  have hsymm : ∀ (n : N) (p : P), e.symm (n, p) = (n : V) + (p : V) := fun n p => rfl
  have hT'apply : ∀ z, T' z = e (T (e.symm z)) := fun z => rfl

  have hdec : ∀ v : V, (((e v).1 : N) : V) + (((e v).2 : P) : V) = v := by
    intro v
    have := e.symm_apply_apply v
    rw [hsymm] at this
    exact this
  have heN : ∀ (v : V) (hv : v ∈ N), e v = (⟨v, hv⟩, 0) := by
    intro v hv
    apply e.symm.injective
    rw [LinearEquiv.symm_apply_apply, hsymm]
    simp

  let A := (LinearMap.fst K N P).comp (T'.comp (LinearMap.inl K N P))
  let D := (LinearMap.snd K N P).comp (T'.comp (LinearMap.inr K N P))
  have h21 : (LinearMap.snd K N P).comp (T'.comp (LinearMap.inl K N P)) = 0 := by
    apply LinearMap.ext
    intro n
    change (e (T (e.symm (n, 0)))).2 = 0
    rw [hsymm, Submodule.coe_zero, add_zero, heN (T n) (hN n.2)]
  have hA : A = T.restrict (p := N) (q := N) (fun x hx => hN hx) := by
    apply LinearMap.ext
    intro n
    apply Subtype.ext
    change (((e (T (e.symm (n, 0)))).1 : N) : V) = T n
    rw [hsymm, Submodule.coe_zero, add_zero, heN (T n) (hN n.2)]
  let q : P ≃ₗ[K] (V ⧸ N) := (Submodule.quotientEquivOfIsCompl N P hNP).symm
  have hq : ∀ p : P, q p = Submodule.Quotient.mk (p : V) := fun p =>
    Submodule.quotientEquivOfIsCompl_symm_apply N P hNP p
  have hD : q.conj D = N.mapQ N T hN := by
    apply LinearMap.ext
    intro z
    obtain ⟨p, rfl⟩ := q.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hq p, Submodule.mapQ_apply, hq (D p)]
    change Submodule.Quotient.mk ((((e (T (e.symm (0, p)))).2 : P) : V)) = Submodule.Quotient.mk (T (p : V))
    rw [hsymm, Submodule.coe_zero, zero_add, Submodule.Quotient.eq]
    have h := hdec (T p)

    have h2 : (((e (T ↑p)).2 : P) : V) - ((((e (T ↑p)).1 : N) : V) + (((e (T ↑p)).2 : P) : V)) =
        -((((e (T ↑p)).1 : N) : V)) := by abel
    rw [h] at h2
    rw [h2]
    exact N.neg_mem (Submodule.coe_mem _)

  let bN := Module.Free.chooseBasis K N
  let bP := Module.Free.chooseBasis K P
  haveI : Fintype (Module.Free.ChooseBasisIndex K N) := Module.Free.ChooseBasisIndex.fintype K N
  haveI : Fintype (Module.Free.ChooseBasisIndex K P) := Module.Free.ChooseBasisIndex.fintype K P
  rw [← hT', ← LinearMap.charpoly_toMatrix T' (bN.prod bP), toMatrix_prod_eq_fromBlocks, h21, map_zero,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  change A.charpoly * D.charpoly = _
  rw [← LinearEquiv.charpoly_conj q D, hD, hA]
  try rfl

end P1Arch

open Polynomial

namespace P1Arch

theorem charpoly_eq_one_of_subsingleton' {K : Type v} [CommRing K] {V : Type w} [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V] [Subsingleton V] (f : V →ₗ[K] V) : f.charpoly = 1 := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · exact Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
      (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

theorem charpoly_pi {K : Type v} [CommRing K] (ι : Type u) [Fintype ι] :
    ∀ (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, Module.Free K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, M i →ₗ[K] M i),
      (LinearMap.pi fun i => (f i).comp (LinearMap.proj i) : (∀ i, M i) →ₗ[K] ∀ i, M i).charpoly =
        ∏ i, (f i).charpoly := by
  refine @Fintype.induction_empty_option
    (fun (α : Type u) [Fintype α] => ∀ (M : α → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, Module.Free K (M i)] [∀ i, Module.Finite K (M i)] (f : ∀ i, M i →ₗ[K] M i),
      (LinearMap.pi fun i => (f i).comp (LinearMap.proj i) : (∀ i, M i) →ₗ[K] ∀ i, M i).charpoly =
        ∏ i, (f i).charpoly) ?_ ?_ ?_ ι inferInstance
  · intro α β _ e hα M _ _ _ _ f
    classical
    letI : Fintype α := Fintype.ofEquiv β e.symm

    let L : (∀ a, M (e a)) ≃ₗ[K] (∀ b, M b) := LinearEquiv.piCongrLeft K M e
    have hconj : L.conj (LinearMap.pi fun a => (f (e a)).comp (LinearMap.proj a)) =
        LinearMap.pi fun i => (f i).comp (LinearMap.proj i) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [LinearEquiv.conj_apply_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      change (Equiv.piCongrLeft M e) _ (e a) = _
      rw [Equiv.piCongrLeft_apply_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      congr 1
    rw [← hconj, LinearEquiv.charpoly_conj, hα (fun a => M (e a)) (fun a => f (e a))]
    exact Fintype.prod_equiv e (fun a => (f (e a)).charpoly) (fun b => (f b).charpoly) (fun a => rfl)
  · intro M _ _ _ _ f
    rw [Fintype.prod_empty]
    exact charpoly_eq_one_of_subsingleton' _
  · intro α _ hα M _ _ _ _ f
    classical
    let L : (∀ i, M i) ≃ₗ[K] (M none × ∀ a, M (some a)) := LinearEquiv.piOptionEquivProd K
    have hconj : L.conj (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        (f none).prodMap (LinearMap.pi fun a => (f (some a)).comp (LinearMap.proj a)) := by
      apply LinearMap.ext
      intro x
      rfl
    rw [← LinearEquiv.charpoly_conj L, hconj, LinearMap.charpoly_prodMap, hα (fun a => M (some a)) (fun a => f (some a)),
      Fintype.prod_option]

scoped instance moduleFinite_localization_atPrime_inst
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (m : MaximalSpectrum A) :
    Module.Finite K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)

theorem charpoly_mulLeft_eq_prod_localization
    (K : Type u) (A : Type u) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [Fintype (MaximalSpectrum A)]
    (a : A) :
    (LinearMap.mulLeft K a).charpoly =
      ∏ m : MaximalSpectrum A,
        (LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a)).charpoly := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let e : A ≃ₗ[K] MaximalSpectrum.PiLocalization A :=
    (MaximalSpectrum.toPiLocalizationEquiv A).toLinearEquiv.restrictScalars K
  have he : ∀ (y : A) (m : MaximalSpectrum A), e y m = algebraMap A (Localization.AtPrime m.asIdeal) y :=
    fun y m => MaximalSpectrum.toPiLocalization_apply_apply A
  have hconj : e.conj (LinearMap.mulLeft K a) =
      LinearMap.pi fun m => (LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a)).comp
        (LinearMap.proj m) := by
    apply LinearMap.ext
    intro x
    funext m
    rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, he, map_mul, ← he (e.symm x) m,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [← LinearEquiv.charpoly_conj e, hconj]
  exact charpoly_pi (K := K) (MaximalSpectrum A) (fun m => Localization.AtPrime m.asIdeal)
    (fun m => LinearMap.mulLeft K (algebraMap A (Localization.AtPrime m.asIdeal) a))

end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

open Polynomial
open scoped TensorProduct

namespace P1Arch

theorem baseChange_mulLeft (W : Type u) [CommRing W] (K : Type v) [CommRing K] [Algebra W K]
    (O : Type u) [CommRing O] [Algebra W O] (a : O) :
    ((LinearMap.mulLeft W a).baseChange K : K ⊗[W] O →ₗ[K] K ⊗[W] O) = LinearMap.mulLeft K ((1 : K) ⊗ₜ[W] a) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k o => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem charpoly_mulLeft_baseChange (W : Type u) [CommRing W] (K : Type v) [CommRing K] [Algebra W K]
    (O : Type u) [CommRing O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    (LinearMap.mulLeft K ((1 : K) ⊗ₜ[W] a) : K ⊗[W] O →ₗ[K] K ⊗[W] O).charpoly =
      Polynomial.map (algebraMap W K) (LinearMap.mulLeft W a).charpoly := by
  rw [← LinearMap.charpoly_baseChange, baseChange_mulLeft]

end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

open Polynomial IsLocalRing

namespace P1Arch

theorem charpoly_eq_one_of_subsingleton {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Subsingleton V] (f : V →ₗ[K] V) : f.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero f.charpoly_monic
    (by rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

theorem charpoly_smul_eq_pow_length
    (K : Type u) (L : Type v) [Field K] [CommRing L] [IsLocalRing L] [Algebra K L]
    [Module.Finite K (ResidueField L)] (a : L)
    (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite K M] :
    (DistribSMul.toLinearMap K M a).charpoly =
      (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly ^ (Module.length L M).toNat := by

  suffices h : ∀ n : ℕ, ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
      [Module.Finite K M], Module.finrank K M = n →
      (DistribSMul.toLinearMap K M a).charpoly =
        (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly ^ (Module.length L M).toNat from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  haveI : IsArtinian L M := isArtinian_of_tower K inferInstance
  haveI : IsNoetherian L M := isNoetherian_of_tower K inferInstance
  by_cases hM : Subsingleton M
  · rw [Module.length_eq_zero_iff.mpr hM, ENat.toNat_zero, pow_zero]
    exact charpoly_eq_one_of_subsingleton _
  have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  obtain ⟨S, hS⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule L M)).resolve_left top_ne_bot
  obtain ⟨hSatom, -⟩ := hS
  haveI hSsimple : IsSimpleModule L S := isSimpleModule_iff_isAtom.mpr hSatom
  obtain ⟨I, hImax, ⟨eS⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSsimple
  have hI : I = maximalIdeal L := IsLocalRing.eq_maximalIdeal hImax
  subst hI

  set T : M →ₗ[K] M := DistribSMul.toLinearMap K M a with hT
  have hTapply : ∀ m : M, T m = a • m := fun m => rfl
  set N : Submodule K M := S.restrictScalars K with hNdef
  have hN : N ≤ N.comap T := fun m hm => S.smul_mem a hm
  rw [charpoly_eq_charpoly_restrict_mul_charpoly_quotient T N hN]

  let e1 : N ≃ₗ[K] ResidueField L :=
    { toFun := fun s => eS ⟨s.1, s.2⟩
      invFun := fun q => ⟨(eS.symm q).1, (eS.symm q).2⟩
      map_add' := fun s t => map_add eS ⟨s.1, s.2⟩ ⟨t.1, t.2⟩
      map_smul' := fun k s => by
        change eS (k • ⟨s.1, s.2⟩) = k • eS ⟨s.1, s.2⟩
        rw [← algebraMap_smul L k, map_smul, algebraMap_smul]
      left_inv := fun s => by
        apply Subtype.ext
        change ((eS.symm (eS ⟨s.1, s.2⟩)) : M) = s.1
        rw [LinearEquiv.symm_apply_apply]
      right_inv := fun q => by
        change eS ⟨(eS.symm q).1, (eS.symm q).2⟩ = q
        exact eS.apply_symm_apply q }
  have he1 : ∀ s : N, e1 s = eS ⟨s.1, s.2⟩ := fun s => rfl
  have h1 : (T.restrict (p := N) (q := N) (fun x hx => hN hx)).charpoly =
      (DistribSMul.toLinearMap K (ResidueField L) (residue L a)).charpoly := by
    rw [← LinearEquiv.charpoly_conj e1]
    congr 1
    apply LinearMap.ext
    intro z
    obtain ⟨s, rfl⟩ := e1.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, he1, he1]
    have hl : (⟨(T.restrict (p := N) (q := N) (fun x hx => hN hx) s).1, (T.restrict (p := N) (q := N) (fun x hx => hN hx) s).2⟩ : S) = a • ⟨s.1, s.2⟩ := rfl
    rw [hl, map_smul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (eS ⟨s.1, s.2⟩)
    rw [← hb]
    change a • Ideal.Quotient.mk (maximalIdeal L) b = Ideal.Quotient.mk (maximalIdeal L) a * Ideal.Quotient.mk (maximalIdeal L) b
    rw [← map_mul]
    rfl

  haveI : Module.Finite K (M ⧸ S) :=
    Module.Finite.of_surjective (S.mkQ.restrictScalars K) (Submodule.mkQ_surjective S)
  have h2 : (N.mapQ N T hN).charpoly = (DistribSMul.toLinearMap K (M ⧸ S) a).charpoly := by
    rw [← LinearEquiv.charpoly_conj (Submodule.Quotient.restrictScalarsEquiv K S)]
    congr 1
    apply LinearMap.ext
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective S z
    rw [LinearEquiv.conj_apply_apply]
    have hsymm : (Submodule.Quotient.restrictScalarsEquiv K S).symm (Submodule.Quotient.mk m) =
        Submodule.Quotient.mk m := rfl
    rw [hsymm, Submodule.mapQ_apply, hTapply]
    rfl

  have hdim : Module.finrank K M = Module.finrank K N + Module.finrank K (M ⧸ S) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv K S).finrank_eq, add_comm]
    exact (Submodule.finrank_quotient_add_finrank N).symm
  have hκpos : 0 < Module.finrank K N := by
    rw [e1.finrank_eq]
    haveI : Nontrivial (ResidueField L) := inferInstance
    exact Module.finrank_pos
  have hlt : Module.finrank K (M ⧸ S) < n := by omega
  have ihq := ih _ hlt (M ⧸ S) rfl

  have hlen : Module.length L M = 1 + Module.length L (M ⧸ S) := by
    rw [Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
      (LinearMap.exact_subtype_mkQ S), Module.length_eq_one_iff.mpr hSsimple]
  haveI : IsArtinian L (M ⧸ S) := isArtinian_of_tower K inferInstance
  haveI : IsNoetherian L (M ⧸ S) := isNoetherian_of_tower K inferInstance
  have hfinq : Module.length L (M ⧸ S) ≠ ⊤ := Module.length_ne_top
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp hfinq
  rw [h1, h2, ihq, hlen, ← hℓ, show (1 : ℕ∞) + (ℓ : ℕ∞) = ((1 + ℓ : ℕ) : ℕ∞) by push_cast; rfl,
    ENat.toNat_coe, ENat.toNat_coe, pow_add, pow_one]

end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

namespace P1Arch
open IsLocalRing Polynomial
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem finrank_quotient_tensor_eq_finrank_quotientK
    (K : Type u) [Field K] (W : Type u) [CommRing W] [IsDomain W] [Algebra W K] [IsFractionRing W K] (B : Type u) [CommRing B] [Algebra W B]
    (𝔪 : Ideal (K ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))] :
    Module.finrank K ((K ⊗[W] B) ⧸ 𝔪) =
      Module.finrank W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B))) := by
  set Q : Ideal B := 𝔪.comap (algebraMap B (K ⊗[W] B)) with hQ
  have halg : ∀ b : B, algebraMap B (K ⊗[W] B) b = (1 : K) ⊗ₜ[W] b := fun b => rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) :=
    IsLocalization.tensorRight K (nonZeroDivisors W)
  have h𝔪 : 𝔪 = Q.map (algebraMap B (K ⊗[W] B)) :=
    (IsLocalization.map_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) 𝔪).symm
  let Q' : Submodule W B := Q.restrictScalars W
  let f : K ⊗[W] Q' →ₗ[K] (K ⊗[W] B) := (Q'.subtype).baseChange K
  let g : (K ⊗[W] B) →ₗ[K] K ⊗[W] (B ⧸ Q') := (Q'.mkQ).baseChange K
  have hftmul : ∀ (k : K) (q : Q'), f (k ⊗ₜ q) = k ⊗ₜ (q : B) := fun k q => by
    simp only [f, LinearMap.baseChange_tmul, Submodule.subtype_apply]
  have hgsurj : Function.Surjective g := by
    change Function.Surjective ((Q'.mkQ).baseChange K)
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective Q')
  have hexact : Function.Exact f g := by
    change Function.Exact ((Q'.subtype).baseChange K) ((Q'.mkQ).baseChange K)
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact K (LinearMap.exact_subtype_mkQ Q') (Submodule.mkQ_surjective Q')
  have hrange : LinearMap.range f = 𝔪.restrictScalars K := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul k q =>
        rw [hftmul, Submodule.restrictScalars_mem]
        have : (k ⊗ₜ[W] (q : B) : K ⊗[W] B) =
            (k ⊗ₜ[W] (1 : B)) * algebraMap B (K ⊗[W] B) q := by
          rw [halg, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        exact 𝔪.mul_mem_left _ (Ideal.mem_comap.mp q.2)
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro x hx
      rw [Submodule.restrictScalars_mem, h𝔪] at hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨q, hq, rfl⟩
        exact ⟨1 ⊗ₜ ⟨q, hq⟩, by rw [hftmul, halg]⟩
      · exact Submodule.zero_mem _
      · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
      · intro a y hymem hy
        obtain ⟨z, rfl⟩ := hy
        clear hymem
        rw [smul_eq_mul]
        induction a using TensorProduct.induction_on with
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | tmul k b =>
          induction z using TensorProduct.induction_on with
          | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
          | tmul k' q =>
            refine ⟨(k * k') ⊗ₜ ⟨b * q, Q.mul_mem_left b q.2⟩, ?_⟩
            rw [hftmul, hftmul, Algebra.TensorProduct.tmul_mul_tmul]
          | add z₁ z₂ h₁ h₂ => rw [map_add, mul_add]; exact Submodule.add_mem _ h₁ h₂
        | add a₁ a₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  let e₁ : ((K ⊗[W] B) ⧸ 𝔪) ≃ₗ[K] ((K ⊗[W] B) ⧸ 𝔪.restrictScalars K) :=
    (Submodule.Quotient.restrictScalarsEquiv K 𝔪).symm
  let e₂ : ((K ⊗[W] B) ⧸ 𝔪.restrictScalars K) ≃ₗ[K]
      ((K ⊗[W] B) ⧸ LinearMap.ker g) :=
    Submodule.quotEquivOfEq _ _ (by rw [← hrange, hexact.linearMap_ker_eq])
  let e₃ : ((K ⊗[W] B) ⧸ LinearMap.ker g) ≃ₗ[K] K ⊗[W] (B ⧸ Q') :=
    g.quotKerEquivOfSurjective hgsurj
  let e₄ : (B ⧸ Q') ≃ₗ[W] (B ⧸ Q) := Submodule.Quotient.restrictScalarsEquiv W Q
  haveI : Module.Free W (B ⧸ Q') := Module.Free.of_equiv e₄.symm
  rw [(e₁.trans (e₂.trans e₃)).finrank_eq, Module.finrank_baseChange, e₄.finrank_eq]

theorem finrank_residueField_localization_eq_finrank_quotientK
    (K : Type u) [Field K] (W : Type u) [CommRing W] [IsDomain W] [Algebra W K] [IsFractionRing W K]
    (B : Type u) [CommRing B] [Algebra W B]
    [Module.Finite K (K ⊗[W] B)]
    (𝔪 : MaximalSpectrum (K ⊗[W] B))
    [Module.Free W (B ⧸ 𝔪.asIdeal.comap (algebraMap B (K ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.asIdeal.comap (algebraMap B (K ⊗[W] B)))] :
    Module.finrank K (ResidueField (Localization.AtPrime 𝔪.asIdeal)) =
      Module.finrank W (B ⧸ 𝔪.asIdeal.comap (algebraMap B (K ⊗[W] B))) := by
  haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  rw [finrank_residueField_localization_eq_finrank_quotient_aux K _ 𝔪.asIdeal]
  exact finrank_quotient_tensor_eq_finrank_quotientK K W B 𝔪.asIdeal

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section GenericH1K
variable {W : Type u} [CommRing W] [IsDomain W]
variable (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
variable (R : Type u) [CommRing R] [Algebra W R] (I : Ideal R)

noncomputable def primeOfMaxK (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) : PrimeSpectrum R :=
  ⟨(𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I), by
    haveI := 𝔪.isMaximal.isPrime
    exact inferInstance⟩

theorem primeOfMaxK_asIdeal (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) :
    (primeOfMaxK K R I 𝔪).asIdeal =
      (𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I) := rfl

theorem primeOfMaxK_injective : Function.Injective (primeOfMaxK (W := W) K R I) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight K (nonZeroDivisors W)
  intro 𝔪₁ 𝔪₂ h
  have h1 := congrArg (fun P : PrimeSpectrum R => (P.asIdeal.map (Ideal.Quotient.mk I)).map
    (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) h
  simp only [primeOfMaxK_asIdeal, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))] at h1
  cases 𝔪₁; cases 𝔪₂; simp only at h1; subst h1; rfl

theorem le_primeOfMaxK (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) : I ≤ (primeOfMaxK K R I 𝔪).asIdeal := by
  intro y hy
  rw [primeOfMaxK_asIdeal, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  exact Ideal.zero_mem _

theorem disjoint_primeOfMaxK (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) :
    Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑(primeOfMaxK K R I 𝔪).asIdeal := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight K (nonZeroDivisors W)
  rw [Set.disjoint_left]
  intro r hr hrP
  obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hr
  rw [SetLike.mem_coe, primeOfMaxK_asIdeal, Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.mk_algebraMap] at hrP
  have hu : IsUnit (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)) (algebraMap W (R ⧸ I) w)) :=
    IsLocalization.map_units (K ⊗[W] (R ⧸ I))
      ⟨algebraMap W (R ⧸ I) w, Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩⟩
  exact 𝔪.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hrP hu)

theorem mem_range_primeOfMaxK [Module.Finite K (K ⊗[W] (R ⧸ I))]
    (P : PrimeSpectrum R) (hIP : I ≤ P.asIdeal)
    (hdisj : Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal) :
    P ∈ Set.range (primeOfMaxK (W := W) K R I) := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight K (nonZeroDivisors W)
  haveI : IsArtinianRing (K ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite K _
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P.asIdeal := by rw [Ideal.mk_ker]; exact hIP
  haveI hPbar : (P.asIdeal.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hback : (P.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hdisj' : Disjoint (↑(Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) : Set (R ⧸ I))
      ↑(P.asIdeal.map (Ideal.Quotient.mk I)) := by
    rw [Set.disjoint_left]
    intro b hb hbP
    obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hb
    rw [SetLike.mem_coe, ← Ideal.Quotient.mk_algebraMap, ← Ideal.mem_comap, hback] at hbP
    exact Set.disjoint_left.mp hdisj (Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩) hbP
  set 𝔪 : Ideal (K ⊗[W] (R ⧸ I)) :=
    (P.asIdeal.map (Ideal.Quotient.mk I)).map (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I))) with h𝔪
  haveI h𝔪p : 𝔪.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPbar hdisj'
  haveI h𝔪m : 𝔪.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔪
  refine ⟨⟨𝔪, h𝔪m⟩, ?_⟩
  ext1
  rw [primeOfMaxK_asIdeal]
  change (Ideal.comap (algebraMap (R ⧸ I) _) 𝔪).comap _ = _
  have hunder : Ideal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I))) 𝔪 = P.asIdeal.map (Ideal.Quotient.mk I) :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) _ hPbar hdisj'
  rw [hunder, hback]

noncomputable def quotQuotEquivK (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) :
    ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) ≃ₗ[W]
      R ⧸ (primeOfMaxK K R I 𝔪).asIdeal := by
  refine ((Ideal.quotientEquivAlgOfEq W ?_).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ W (le_primeOfMaxK K R I 𝔪))).toLinearEquiv

  rw [primeOfMaxK_asIdeal]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ W I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) =
      Ideal.map (Ideal.Quotient.mk I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem finrank_localization_atPrime_eqK [Module.Finite K (K ⊗[W] (R ⧸ I))]
    (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I)))
    (hfin : Module.Finite W (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal)) (hfree : Module.Free W (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal)) :
    (Module.finrank K (Localization.AtPrime 𝔪.asIdeal) : ℕ∞) =
      (Module.finrank W (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime (primeOfMaxK K R I 𝔪).asIdeal)
          (LocalizedModule (primeOfMaxK K R I 𝔪).asIdeal.primeCompl (R ⧸ I)) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight K (nonZeroDivisors W)
  haveI := 𝔪.isMaximal.isPrime
  haveI : Module.Finite K (Localization.AtPrime 𝔪.asIdeal) :=
    moduleFinite_localization_atPrime_of_moduleFinite K _ 𝔪
  haveI : Module.Finite W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) :=
    Module.Finite.equiv (quotQuotEquivK K R I 𝔪).symm
  haveI : Module.Free W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) :=
    Module.Free.of_equiv (quotQuotEquivK K R I 𝔪).symm
  rw [finrank_eq_finrank_residueField_mul_length K (Localization.AtPrime 𝔪.asIdeal)
      (Localization.AtPrime 𝔪.asIdeal),
    finrank_residueField_localization_eq_finrank_quotientK K W (R ⧸ I) 𝔪,
    (quotQuotEquivK K R I 𝔪).finrank_eq,
    length_localization_atPrime_eq_of_isLocalization (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))
      (K ⊗[W] (R ⧸ I)) 𝔪.asIdeal]
  congr 1
  exact (length_localizedModule_quotient_eq_length_localization R I _).symm

theorem finrank_tensor_quotient_eq_finsum_genericK [Module.Finite K (K ⊗[W] (R ⧸ I))]
    (hff : ∀ P : PrimeSpectrum R, I ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    (Module.finrank K (K ⊗[W] (R ⧸ I)) : ℕ∞) =
      ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
          Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
        (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ I)) := by
  classical
  haveI : IsArtinianRing (K ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite K _
  haveI : Finite (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := IsArtinianRing.instFiniteMaximalSpectrum _
  letI : Fintype (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := Fintype.ofFinite _
  have hrange : Set.range (primeOfMaxK (W := W) K R I) = {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal} := by
    ext P
    constructor
    · rintro ⟨𝔪, rfl⟩
      exact ⟨le_primeOfMaxK K R I 𝔪, disjoint_primeOfMaxK K R I 𝔪⟩
    · rintro ⟨h1, h2⟩
      exact mem_range_primeOfMaxK K R I P h1 h2
  rw [← hrange, finsum_mem_range (primeOfMaxK_injective K R I), finsum_eq_sum_of_fintype,
    finrank_eq_sum_finrank_localization_atPrime K (K ⊗[W] (R ⧸ I)), Nat.cast_sum]
  refine Finset.sum_congr rfl fun 𝔪 _ => ?_
  obtain ⟨hfin, hfree⟩ := hff (primeOfMaxK K R I 𝔪) (le_primeOfMaxK K R I 𝔪) (disjoint_primeOfMaxK K R I 𝔪)
  exact finrank_localization_atPrime_eqK K R I 𝔪 hfin hfree

end GenericH1K
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
section ResidueAlgEquiv

noncomputable def quotMaxAlgEquivResidueField
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    (A ⧸ 𝔪) ≃ₐ[K] ResidueField (Localization.AtPrime 𝔪) := by
  let ρ : A →+* ResidueField (Localization.AtPrime 𝔪) :=
    (residue (Localization.AtPrime 𝔪)).comp (algebraMap A (Localization.AtPrime 𝔪))
  have hρ : ∀ a ∈ 𝔪, ρ a = 0 := by
    intro a ha
    change residue _ (algebraMap A (Localization.AtPrime 𝔪) a) = 0
    rw [residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mpr ha
  let ψ₀ : (A ⧸ 𝔪) →+* ResidueField (Localization.AtPrime 𝔪) := Ideal.Quotient.lift 𝔪 ρ hρ
  have hψmk : ∀ a : A, ψ₀ (Ideal.Quotient.mk _ a) = residue _ (algebraMap A (Localization.AtPrime 𝔪) a) :=
    fun a => rfl
  have hKL : ∀ k : K, algebraMap K (ResidueField (Localization.AtPrime 𝔪)) k =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) (algebraMap K A k)) := by
    intro k
    rw [← IsScalarTower.algebraMap_apply K A (Localization.AtPrime 𝔪) k,
      IsScalarTower.algebraMap_apply K (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) k,
      ResidueField.algebraMap_eq]
  let ψ : (A ⧸ 𝔪) →ₐ[K] ResidueField (Localization.AtPrime 𝔪) := AlgHom.mk' ψ₀ (by
    intro k x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Algebra.smul_def, hKL, ← hψmk, ← map_mul, IsScalarTower.algebraMap_apply K A (A ⧸ 𝔪) k,
      Ideal.Quotient.algebraMap_eq, ← map_mul])
  refine AlgEquiv.ofBijective ψ ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change ψ₀ _ = 0 at hz
    rw [hψmk, residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl l
    have hs0 : (Ideal.Quotient.mk 𝔪 (s : A)) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact s.2
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ t', ?_⟩
    have hsunit : residue _ (algebraMap A (Localization.AtPrime 𝔪) s) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪]
      exact s.2
    apply mul_right_cancel₀ hsunit
    dsimp only
    change ψ₀ _ * _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔪) a s) *
      residue _ (algebraMap A (Localization.AtPrime 𝔪) s)
    have hts : Ideal.Quotient.mk 𝔪 t' * Ideal.Quotient.mk 𝔪 (s : A) = 1 := by
      rw [mul_comm]; exact ht
    rw [← map_mul (residue _), IsLocalization.mk'_spec, ← hψmk a, ← hψmk (s : A), ← map_mul ψ₀, mul_assoc,
      hts, mul_one]

theorem quotMaxAlgEquivResidueField_mk
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] (a : A) :
    quotMaxAlgEquivResidueField K A 𝔪 (Ideal.Quotient.mk 𝔪 a) =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) a) := rfl

end ResidueAlgEquiv
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
section QuotTensorK
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K : Type u) [Field K] (W : Type u) [CommRing W] [IsDomain W] [Algebra W K] [IsFractionRing W K] (B : Type u) [CommRing B] [Algebra W B]

noncomputable def quotMaxAlgEquivTensorQuotK
    [Module.Finite K (K ⊗[W] B)]
    (𝔪 : Ideal (K ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))] :
    ((K ⊗[W] B) ⧸ 𝔪) ≃ₐ[K]
      K ⊗[W] (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B))) := by
  set Q : Ideal B := 𝔪.comap (algebraMap B (K ⊗[W] B)) with hQ
  let g : (K ⊗[W] B) →ₐ[K] K ⊗[W] (B ⧸ Q) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ W Q)
  have hg : ∀ z ∈ 𝔪, g z = 0 := by
    haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) :=
      IsLocalization.tensorRight K (nonZeroDivisors W)
    have h𝔪 : 𝔪 = Q.map (algebraMap B (K ⊗[W] B)) :=
      (IsLocalization.map_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) 𝔪).symm
    intro z hz
    rw [h𝔪] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      change g ((1 : K) ⊗ₜ[W] q) = 0
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hq, TensorProduct.tmul_zero]
    · exact map_zero g
    · intro y z _ _ hy hz; rw [map_add, hy, hz, add_zero]
    · intro a y _ hy; rw [smul_eq_mul, map_mul, hy, mul_zero]
  let Φ : ((K ⊗[W] B) ⧸ 𝔪) →ₐ[K] K ⊗[W] (B ⧸ Q) :=
    Ideal.Quotient.liftₐ 𝔪 g hg
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨y, rfl⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id K K)
      (Ideal.Quotient.mkₐ W Q) Function.surjective_id Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  haveI : Module.Finite K ((K ⊗[W] B) ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  have hdim : Module.finrank K ((K ⊗[W] B) ⧸ 𝔪) =
      Module.finrank K (K ⊗[W] (B ⧸ Q)) := by
    rw [finrank_quotient_tensor_eq_finrank_quotientK K W B 𝔪, Module.finrank_baseChange]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).mpr hsurj
  exact AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩

theorem quotMaxAlgEquivTensorQuotK_mk_tmul
    [Module.Finite K (K ⊗[W] B)]
    (𝔪 : Ideal (K ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))] (k : K) (b : B) :
    quotMaxAlgEquivTensorQuotK K W B 𝔪 (Ideal.Quotient.mk 𝔪 (k ⊗ₜ[W] b)) = k ⊗ₜ[W] Ideal.Quotient.mk _ b := by
  change Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ W _) (k ⊗ₜ b) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

end QuotTensorK
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
section ConjLemmas

theorem charpoly_mulLeft_algEquiv {K : Type u} [CommRing K] {B : Type v} {C : Type w} [Ring B] [Ring C]
    [Algebra K B] [Algebra K C] [Module.Free K B] [Module.Finite K B] [Module.Free K C] [Module.Finite K C]
    (Φ : B ≃ₐ[K] C) (b : B) :
    (LinearMap.mulLeft K b).charpoly = (LinearMap.mulLeft K (Φ b)).charpoly := by
  rw [← LinearEquiv.charpoly_conj Φ.toLinearEquiv (LinearMap.mulLeft K b)]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearEquiv_apply,
    map_mul]
  congr 1
  exact Φ.toLinearEquiv.apply_symm_apply z

theorem mulLeft_eq_toLinearMap {K : Type u} [CommRing K] {L : Type v} [CommRing L] [Algebra K L] (a : L) :
    (LinearMap.mulLeft K a : L →ₗ[K] L) = DistribSMul.toLinearMap K L a := by
  apply LinearMap.ext; intro z; rfl

theorem moduleFinite_residueField (K : Type u) [Field K] (L : Type v) [CommRing L] [IsLocalRing L] [Algebra K L]
    [Module.Finite K L] : Module.Finite K (ResidueField L) :=
  Module.Finite.of_surjective (IsScalarTower.toAlgHom K L (ResidueField L)).toLinearMap Ideal.Quotient.mk_surjective

end ConjLemmas
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
section QuotQuotK
variable {W : Type u} [CommRing W] [IsDomain W]
variable (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
variable (R : Type u) [CommRing R] [Algebra W R] (I : Ideal R)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable def quotQuotAlgEquivK (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) :
    ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) ≃ₐ[W]
      R ⧸ (primeOfMaxK K R I 𝔪).asIdeal := by
  refine (Ideal.quotientEquivAlgOfEq W ?_).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ W (le_primeOfMaxK K R I 𝔪))
  rw [primeOfMaxK_asIdeal]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ W I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) =
      Ideal.map (Ideal.Quotient.mk I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem quotQuotAlgEquivK_mk_mk (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I))) (r : R) :
    quotQuotAlgEquivK K R I 𝔪 (Ideal.Quotient.mk _ (Ideal.Quotient.mk I r)) =
      Ideal.Quotient.mk (primeOfMaxK K R I 𝔪).asIdeal r := by
  unfold quotQuotAlgEquivK
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r (le_primeOfMaxK K R I 𝔪)

end QuotQuotK
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

namespace P1Arch
open IsLocalRing Polynomial
open scoped TensorProduct

section LocalFactorK
variable {W : Type u} [CommRing W] [IsDomain W]
variable (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
variable (R : Type u) [CommRing R] [Algebra W R] (I : Ideal R) (u : R)

theorem charpoly_mulLeft_localization_eq_powK [Module.Finite K (K ⊗[W] (R ⧸ I))]
    (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ I)))
    [Module.Finite W (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal)] [Module.Free W (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal)]
    [Module.Free K (Localization.AtPrime 𝔪.asIdeal)] [Module.Finite K (Localization.AtPrime 𝔪.asIdeal)] :
    LinearMap.charpoly (R := K) (M := Localization.AtPrime 𝔪.asIdeal) (LinearMap.mulLeft K
        (algebraMap (K ⊗[W] (R ⧸ I)) (Localization.AtPrime 𝔪.asIdeal)
          ((1 : K) ⊗ₜ[W] Ideal.Quotient.mk I u))) =
      (Polynomial.map (algebraMap W K)
        (LinearMap.mulLeft W (Ideal.Quotient.mk (primeOfMaxK K R I 𝔪).asIdeal u)).charpoly) ^
        (Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal)).toNat := by
  letI : Algebra (R ⧸ I) (K ⊗[W] (R ⧸ I)) := Algebra.TensorProduct.rightAlgebra
  haveI h𝔪max : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  haveI : Module.Finite K (ResidueField (Localization.AtPrime 𝔪.asIdeal)) :=
    moduleFinite_residueField K (Localization.AtPrime 𝔪.asIdeal)
  set aL := algebraMap (K ⊗[W] (R ⧸ I)) (Localization.AtPrime 𝔪.asIdeal)
    ((1 : K) ⊗ₜ[W] Ideal.Quotient.mk I u) with haL

  rw [mulLeft_eq_toLinearMap, charpoly_smul_eq_pow_length K (Localization.AtPrime 𝔪.asIdeal) aL
    (Localization.AtPrime 𝔪.asIdeal)]
  congr 1
  rw [← mulLeft_eq_toLinearMap]

  haveI : Module.Finite W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) :=
    Module.Finite.equiv (quotQuotAlgEquivK K R I 𝔪).toLinearEquiv.symm
  haveI : Module.Free W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) (K ⊗[W] (R ⧸ I)))) :=
    Module.Free.of_equiv (quotQuotAlgEquivK K R I 𝔪).toLinearEquiv.symm
  let Ψ : ResidueField (Localization.AtPrime 𝔪.asIdeal) ≃ₐ[K]
      K ⊗[W] (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal) :=
    (quotMaxAlgEquivResidueField K _ 𝔪.asIdeal).symm.trans
      ((quotMaxAlgEquivTensorQuotK K W (R ⧸ I) 𝔪.asIdeal).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl (quotQuotAlgEquivK K R I 𝔪)))
  rw [charpoly_mulLeft_algEquiv Ψ]
  have h1 : (quotMaxAlgEquivResidueField K _ 𝔪.asIdeal).symm
      (residue (Localization.AtPrime 𝔪.asIdeal) aL) =
      Ideal.Quotient.mk 𝔪.asIdeal ((1 : K) ⊗ₜ[W] Ideal.Quotient.mk I u) := by
    apply (quotMaxAlgEquivResidueField K _ 𝔪.asIdeal).injective
    rw [AlgEquiv.apply_symm_apply, quotMaxAlgEquivResidueField_mk]
  have hΨ : Ψ (residue (Localization.AtPrime 𝔪.asIdeal) aL) =
      (1 : K) ⊗ₜ[W] Ideal.Quotient.mk (primeOfMaxK K R I 𝔪).asIdeal u := by
    change (Algebra.TensorProduct.congr AlgEquiv.refl (quotQuotAlgEquivK K R I 𝔪))
      (quotMaxAlgEquivTensorQuotK K W (R ⧸ I) 𝔪.asIdeal
        ((quotMaxAlgEquivResidueField K _ 𝔪.asIdeal).symm
          (residue (Localization.AtPrime 𝔪.asIdeal) aL))) = _
    rw [h1, quotMaxAlgEquivTensorQuotK_mk_tmul, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    change (1 : K) ⊗ₜ[W] quotQuotAlgEquivK K R I 𝔪 (Ideal.Quotient.mk _ (Ideal.Quotient.mk I u)) = _
    rw [quotQuotAlgEquivK_mk_mk]
  rw [hΨ]
  exact charpoly_mulLeft_baseChange W K (R ⧸ (primeOfMaxK K R I 𝔪).asIdeal) _

end LocalFactorK
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

namespace P1Arch
open IsLocalRing Polynomial

theorem charpoly_mulLeft_isPureSlope_of_isDomain {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    IsPureSlope (Module.finrank W O) (Algebra.norm W a) (Module.finrank W O) (LinearMap.mulLeft W a).charpoly :=
  IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete O a
end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

namespace P1Arch
open IsLocalRing Polynomial
open scoped TensorProduct

section HeadsDefs
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

variable (W)
variable (R : Type u) [CommRing R] [Algebra W R] (x u : R)

noncomputable def rankQuot (P : PrimeSpectrum R) : ℕ := Module.finrank W (R ⧸ P.asIdeal)
noncomputable def normU (P : PrimeSpectrum R) : W := Algebra.norm W (Ideal.Quotient.mk P.asIdeal u)
variable {W}
noncomputable def lenAt (P : PrimeSpectrum R) : ℕ :=
  (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat

end HeadsDefs
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

section Assembly
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable (R : Type u) [CommRing R] [Algebra W R] (x u : R)

theorem lenAt_primeOfMaxK_eq (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
    [Module.Finite K (K ⊗[W] (R ⧸ Ideal.span {x}))]
    (𝔪 : MaximalSpectrum (K ⊗[W] (R ⧸ Ideal.span {x}))) :
    (lenAt R x (primeOfMaxK K R (Ideal.span {x}) 𝔪) : ℕ∞) =
      Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal) := by
  letI : Algebra (R ⧸ Ideal.span {x}) (K ⊗[W] (R ⧸ Ideal.span {x})) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {x}) (nonZeroDivisors W))
      (K ⊗[W] (R ⧸ Ideal.span {x})) := IsLocalization.tensorRight K (nonZeroDivisors W)
  haveI := 𝔪.isMaximal.isPrime
  haveI : IsArtinianRing (K ⊗[W] (R ⧸ Ideal.span {x})) := IsArtinianRing.of_finite K _
  have hlen : Module.length (Localization.AtPrime (primeOfMaxK K R (Ideal.span {x}) 𝔪).asIdeal)
      (LocalizedModule (primeOfMaxK K R (Ideal.span {x}) 𝔪).asIdeal.primeCompl (R ⧸ Ideal.span {x})) =
      Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal) := by
    rw [length_localization_atPrime_eq_of_isLocalization (R ⧸ Ideal.span {x})
      (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {x}) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ Ideal.span {x})) 𝔪.asIdeal]
    exact length_localizedModule_quotient_eq_length_localization R (Ideal.span {x}) _
  have hfin : Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal) ≠ ⊤ :=
    Module.length_ne_top
  unfold lenAt
  rw [hlen]
  exact ENat.coe_toNat hfin

theorem charpoly_mulLeft_eq_finprod_pureSlopeK (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
    [IsAdicComplete (maximalIdeal W) W]
    [Module.Free W (R ⧸ Ideal.span {x})] [Module.Finite W (R ⧸ Ideal.span {x})]
    [Module.Finite K (K ⊗[W] (R ⧸ Ideal.span {x}))]
    (hff : ∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    ∃ χP : PrimeSpectrum R → Polynomial W,
      (∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
        Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
          IsPureSlope (rankQuot W R P) (normU W R u P) (rankQuot W R P * lenAt R x P) (χP P)) ∧
      (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) u)).charpoly =
        ∏ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}), χP P ∧
      Module.finrank W (R ⧸ Ideal.span {x}) =
        ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
          rankQuot W R P * lenAt R x P := by
  classical
  set I : Ideal R := Ideal.span {x} with hI
  set S : Set (PrimeSpectrum R) := {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
    Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal} with hS

  let χP : PrimeSpectrum R → Polynomial W := fun P =>
    if h : P ∈ S then
      (haveI := (hff P h.1 h.2).1; haveI := (hff P h.1 h.2).2;
        (LinearMap.mulLeft W (Ideal.Quotient.mk P.asIdeal u)).charpoly) ^ lenAt R x P
    else 1
  have hχP : ∀ P (h : P ∈ S), χP P = (haveI := (hff P h.1 h.2).1; haveI := (hff P h.1 h.2).2;
      (LinearMap.mulLeft W (Ideal.Quotient.mk P.asIdeal u)).charpoly) ^ lenAt R x P := by
    intro P h
    simp only [χP, dif_pos h]
  refine ⟨χP, ?_, ?_, ?_⟩
  ·
    intro P h1 h2
    have h : P ∈ S := ⟨h1, h2⟩
    rw [hχP P h]
    haveI := (hff P h1 h2).1
    haveI := (hff P h1 h2).2
    exact (charpoly_mulLeft_isPureSlope_of_isDomain (W := W) (R ⧸ P.asIdeal) (Ideal.Quotient.mk P.asIdeal u)).pow
      (lenAt R x P)
  ·
    letI : Algebra (R ⧸ I) (K ⊗[W] (R ⧸ I)) := Algebra.TensorProduct.rightAlgebra
    haveI : IsArtinianRing (K ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite K _
    haveI : Finite (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := IsArtinianRing.instFiniteMaximalSpectrum _
    letI : Fintype (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := Fintype.ofFinite _
    have hrange : Set.range (primeOfMaxK (W := W) K R I) = S := by
      ext P
      constructor
      · rintro ⟨𝔪, rfl⟩
        exact ⟨le_primeOfMaxK K R I 𝔪, disjoint_primeOfMaxK K R I 𝔪⟩
      · rintro ⟨h1, h2⟩
        exact mem_range_primeOfMaxK K R I P h1 h2
    apply Polynomial.map_injective (algebraMap W K) (IsFractionRing.injective W K)
    rw [← hrange, finprod_mem_range (primeOfMaxK_injective K R I), finprod_eq_prod_of_fintype, Polynomial.map_prod,
      ← charpoly_mulLeft_baseChange W K (R ⧸ I) (Ideal.Quotient.mk I u),
      charpoly_mulLeft_eq_prod_localization K (K ⊗[W] (R ⧸ I)) ((1 : K) ⊗ₜ[W] Ideal.Quotient.mk I u)]
    refine Finset.prod_congr rfl fun 𝔪 _ => ?_
    haveI := (hff _ (le_primeOfMaxK K R I 𝔪) (disjoint_primeOfMaxK K R I 𝔪)).1
    haveI := (hff _ (le_primeOfMaxK K R I 𝔪) (disjoint_primeOfMaxK K R I 𝔪)).2
    haveI : Module.Free K (Localization.AtPrime 𝔪.asIdeal) :=
      Module.Free.of_divisionRing K (Localization.AtPrime 𝔪.asIdeal)
    rw [charpoly_mulLeft_localization_eq_powK K R I u 𝔪, hχP _ ⟨le_primeOfMaxK K R I 𝔪, disjoint_primeOfMaxK K R I 𝔪⟩,
      Polynomial.map_pow]
    congr 1
    apply Nat.cast_injective (R := ℕ∞)
    rw [lenAt_primeOfMaxK_eq R x K 𝔪]
    exact ENat.coe_toNat (Module.length_ne_top (R := Localization.AtPrime 𝔪.asIdeal)
      (M := Localization.AtPrime 𝔪.asIdeal))
  ·
    letI : Algebra (R ⧸ I) (K ⊗[W] (R ⧸ I)) := Algebra.TensorProduct.rightAlgebra
    haveI : IsArtinianRing (K ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite K _
    haveI : Finite (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := IsArtinianRing.instFiniteMaximalSpectrum _
    letI : Fintype (MaximalSpectrum (K ⊗[W] (R ⧸ I))) := Fintype.ofFinite _
    have hrange : Set.range (primeOfMaxK (W := W) K R I) = S := by
      ext P
      constructor
      · rintro ⟨𝔪, rfl⟩
        exact ⟨le_primeOfMaxK K R I 𝔪, disjoint_primeOfMaxK K R I 𝔪⟩
      · rintro ⟨h1, h2⟩
        exact mem_range_primeOfMaxK K R I P h1 h2
    rw [← hrange, finsum_mem_range (primeOfMaxK_injective K R I), finsum_eq_sum_of_fintype,
      ← Module.finrank_baseChange (R := K),
      finrank_eq_sum_finrank_localization_atPrime K (K ⊗[W] (R ⧸ I))]
    refine Finset.sum_congr rfl fun 𝔪 _ => ?_
    obtain ⟨hfin, hfree⟩ := hff _ (le_primeOfMaxK K R I 𝔪) (disjoint_primeOfMaxK K R I 𝔪)
    apply Nat.cast_injective (R := ℕ∞)
    rw [finrank_localization_atPrime_eqK K R I 𝔪 hfin hfree, Nat.cast_mul, lenAt_primeOfMaxK_eq R x K 𝔪]
    congr 1
    haveI := 𝔪.isMaximal.isPrime
    haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) :=
      IsLocalization.tensorRight K (nonZeroDivisors W)
    rw [length_localization_atPrime_eq_of_isLocalization (R ⧸ I)
      (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) (K ⊗[W] (R ⧸ I)) 𝔪.asIdeal]
    exact length_localizedModule_quotient_eq_length_localization R I _

theorem length_localizedModule_quotient_lt_top [Module.Finite W (R ⧸ Ideal.span {x})] (P : PrimeSpectrum R)
    (hxP : Ideal.span {x} ≤ P.asIdeal)
    (hdisj : Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal) :
    Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x})) < ⊤ := by
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x})) :=
    Module.Finite.base_change W (FractionRing W) (R ⧸ Ideal.span {x})
  obtain ⟨𝔪, h𝔪⟩ := mem_range_primeOfMaxK (FractionRing W) R (Ideal.span {x}) P hxP hdisj
  subst h𝔪
  letI : Algebra (R ⧸ Ideal.span {x}) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x})) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {x}) (nonZeroDivisors W))
      ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x})) := IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI := 𝔪.isMaximal.isPrime
  haveI : IsArtinianRing ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x})) := IsArtinianRing.of_finite (FractionRing W) _
  have h2 : Module.length (Localization.AtPrime (primeOfMaxK (FractionRing W) R (Ideal.span {x}) 𝔪).asIdeal)
      (LocalizedModule (primeOfMaxK (FractionRing W) R (Ideal.span {x}) 𝔪).asIdeal.primeCompl (R ⧸ Ideal.span {x})) =
      Module.length (Localization.AtPrime 𝔪.asIdeal) (Localization.AtPrime 𝔪.asIdeal) := by
    rw [length_localization_atPrime_eq_of_isLocalization (R ⧸ Ideal.span {x})
      (Algebra.algebraMapSubmonoid (R ⧸ Ideal.span {x}) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x})) 𝔪.asIdeal]
    exact length_localizedModule_quotient_eq_length_localization R (Ideal.span {x}) _
  rw [h2, lt_top_iff_ne_top]
  exact Module.length_ne_top (R := Localization.AtPrime 𝔪.asIdeal) (M := Localization.AtPrime 𝔪.asIdeal)

theorem charpoly_mulLeft_eq_finprod_pureSlope [IsAdicComplete (maximalIdeal W) W]
    [Module.Free W (R ⧸ Ideal.span {x})] [Module.Finite W (R ⧸ Ideal.span {x})]
    [Module.Finite (FractionRing W) (TensorProduct W (FractionRing W) (R ⧸ Ideal.span {x}))]
    (hff : ∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    ∃ χP : PrimeSpectrum R → Polynomial W,
      (∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
        Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
          IsPureSlope (rankQuot W R P) (normU W R u P) (rankQuot W R P * lenAt R x P) (χP P)) ∧
      (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) u)).charpoly =
        ∏ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}), χP P ∧
      Module.finrank W (R ⧸ Ideal.span {x}) =
        ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
          rankQuot W R P * lenAt R x P :=
  charpoly_mulLeft_eq_finprod_pureSlopeK R x u (FractionRing W) hff

end Assembly
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"
end P1Arch
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope.P1Arch"

open IsLocalRing Polynomial
open scoped TensorProduct

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (R : Type u) [CommRing R] [Algebra W R] (x u : R)
    [Module.Free W (R ⧸ Ideal.span {x})] [Module.Finite W (R ⧸ Ideal.span {x})]
    (hff : ∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    ∃ χP : PrimeSpectrum R → Polynomial W,
      (∀ P : PrimeSpectrum R, Ideal.span {x} ≤ P.asIdeal →
        Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
          (χP P).Monic ∧ (χP P).natDegree = (Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) ∧
          (∀ i : ℕ, i ≤ (Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) →
            (((Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W (Ideal.Quotient.mk P.asIdeal u)) ≤
              (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) * IsDiscreteValuationRing.addVal W ((χP P).coeff i)) ∧
          (((Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W (Ideal.Quotient.mk P.asIdeal u)) =
            (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) * IsDiscreteValuationRing.addVal W ((χP P).coeff 0))) ∧
      (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) u)).charpoly =
        ∏ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}), χP P ∧
      Module.finrank W (R ⧸ Ideal.span {x}) =
        ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | Ideal.span {x} ≤ P.asIdeal ∧
            Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
          Module.finrank W (R ⧸ P.asIdeal) * (Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ Ideal.span {x}))).toNat := by
  haveI : Module.Finite (FractionRing W) (TensorProduct W (FractionRing W) (R ⧸ Ideal.span {x})) :=
    Module.Finite.base_change W (FractionRing W) (R ⧸ Ideal.span {x})
  exact P1Arch.charpoly_mulLeft_eq_finprod_pureSlope R x u hff

end S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope
end P2MW
export P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope (solution)
