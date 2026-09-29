-- Prove2me | solution 1 for HopfAlgebra.map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0b488bba-f86c-5255-bab5-59767dc988c4

import Mathlib
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v w

namespace ETQfBody

section Idem

variable {R : Type*} [CommRing R]

private theorem mem_span_one_sub_iff {e : R} (he : IsIdempotentElem e) (x : R) :
    x ∈ Ideal.span {1 - e} ↔ x * e = 0 := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    rw [mul_assoc, sub_mul, one_mul, he.eq, sub_self, mul_zero]
  · intro h
    exact ⟨x, by rw [mul_sub, mul_one, h, sub_zero]⟩

private theorem isReduced_quotient_span_one_sub [IsReduced R] {e : R} (he : IsIdempotentElem e) :
    IsReduced (R ⧸ Ideal.span {1 - e}) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_span_one_sub_iff he] at hn
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_one_sub_iff he]
  cases n with
  | zero =>
    rw [pow_zero, one_mul] at hn
    rw [hn, mul_zero]
  | succ n =>
    have : (r * e) ^ (n + 1) = 0 := by rw [mul_pow, he.pow_succ_eq, hn]
    exact IsReduced.eq_zero _ ⟨n + 1, this⟩

private theorem eq_zero_or_one_of_isLocalRing [IsLocalRing R] {u : R} (hu : IsIdempotentElem u) :
    u = 0 ∨ u = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self u with h | h
  · right
    obtain ⟨v, hv⟩ := h.exists_left_inv
    calc u = v * u * u := by rw [hv, one_mul]
      _ = v * u := by rw [mul_assoc, hu.eq]
      _ = 1 := hv
  · left
    obtain ⟨v, hv⟩ := h.exists_left_inv
    calc u = v * (1 - u) * u := by rw [hv, one_mul]
      _ = 0 := by rw [mul_assoc, sub_mul, one_mul, hu.eq, sub_self, mul_zero]

end Idem

section Base

variable {𝓞 : Type u} [CommRing 𝓞]

private theorem henselianLocalRing_of_isAdicComplete [IsLocalRing 𝓞] (I : Ideal 𝓞) [IsAdicComplete I 𝓞]
    (hI : IsLocalRing.maximalIdeal 𝓞 = I) : HenselianLocalRing 𝓞 where
  is_henselian f hf a₀ h₁ h₂ := by
    have hH : HenselianRing 𝓞 I := inferInstance
    rw [hI] at h₁ ⊢
    exact hH.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk I))

private theorem isLocalRing_of_forall_isIdempotentElem [HenselianLocalRing 𝓞] {S : Type*} [CommRing S]
    [Algebra 𝓞 S] [Module.Finite 𝓞 S] [Nontrivial S]
    (h : ∀ u : S, IsIdempotentElem u → u = 0 ∨ u = 1) : IsLocalRing S := by
  obtain ⟨_, e, hce, hnot, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := 𝓞) (S := S)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  let m₀ : MaximalSpectrum S := ⟨m, hm⟩
  have he1 : e m₀ = 1 := by
    rcases h (e m₀) (hce.idem m₀) with h0 | h1
    · exact absurd (h0 ▸ Ideal.zero_mem _) (hnot m₀)
    · exact h1
  have hbot : Ideal.span {1 - e m₀} = ⊥ := by rw [he1, sub_self, Ideal.span_singleton_zero]
  haveI := hloc m₀
  let g : S ⧸ Ideal.span {1 - e m₀} →+* S :=
    Ideal.Quotient.lift _ (RingHom.id S) fun a ha => by rwa [hbot, Ideal.mem_bot] at ha
  exact IsLocalRing.of_surjective' g fun s => ⟨Ideal.Quotient.mk _ s, rfl⟩

end Base

section Reduction

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)] (T : Type*) [CommRing T] [Algebra 𝓞 T]

private noncomputable abbrev red : T →ₐ[𝓞] ZMod p ⊗[𝓞] T := Algebra.TensorProduct.includeRight

variable {𝓞 p T}

private theorem red_apply (a : T) : red 𝓞 p T a = (1 : ZMod p) ⊗ₜ[𝓞] a := rfl

private theorem red_surjective (hk : Surjective (algebraMap 𝓞 (ZMod p))) : Surjective (red 𝓞 p T) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨o, rfl⟩ := hk c
    refine ⟨o • a, ?_⟩
    rw [red_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

private theorem natCast_eq_zero : (p : ZMod p ⊗[𝓞] T) = 0 := by
  rw [Algebra.TensorProduct.natCast_def, ZMod.natCast_self, TensorProduct.zero_tmul]

private theorem ker_red (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (red 𝓞 p T : T →ₐ[𝓞] ZMod p ⊗[𝓞] T) = Ideal.span {(p : T)} := by
  apply le_antisymm
  · set J : Ideal T := Ideal.span {(p : T)} with hJ
    have hle : RingHom.ker (algebraMap 𝓞 (ZMod p)) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 T)) := by
      intro o ho
      rw [hker] at ho
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    let κ₀ : ZMod p →+* T ⧸ J := (algebraMap 𝓞 (ZMod p)).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 (ZMod p) o) = Ideal.Quotient.mk J (algebraMap 𝓞 T o) := fun o =>
      (algebraMap 𝓞 (ZMod p)).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : ZMod p →ₐ[𝓞] T ⧸ J := { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
    let Ψ : ZMod p ⊗[𝓞] T →ₐ[𝓞] T ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro a ha
    rw [RingHom.mem_ker] at ha
    have h1 : Ψ (red 𝓞 p T a) = Ideal.Quotient.mk J a := by
      rw [red_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    rw [show red 𝓞 p T a = 0 from ha, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    exact natCast_eq_zero

end Reduction

end ETQfBody

open ETQfBody in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [HopfAlgebra 𝓞 H] [Module.Finite 𝓞 H] (hred : IsReduced (ZMod p ⊗[𝓞] H))
    (L : Type w) [CommRing L] [HopfAlgebra 𝓞 L] (j : H →ₐc[𝓞] L) (hj : Function.Injective j)
    (f : H) (hf : IsIdempotentElem f) (hεf : Coalgebra.counit (R := 𝓞) f = 1)
    (hloc : IsLocalRing (L ⧸ Ideal.span {1 - j f})) :
    Ideal.map (j : H →ₐ[𝓞] L) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 H)) = Ideal.span {1 - j f} := by
  classical
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  obtain ⟨_, _, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞 := by rw [hmax]; infer_instance
  haveI : HenselianLocalRing 𝓞 := henselianLocalRing_of_isAdicComplete (IsLocalRing.maximalIdeal 𝓞) rfl

  set I : Ideal H := Ideal.span {1 - f} with hIdef
  apply le_antisymm
  swap
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h1f : 1 - f ∈ RingHom.ker (Bialgebra.counitAlgHom 𝓞 H) := by
      rw [RingHom.mem_ker, map_sub, map_one, Bialgebra.counitAlgHom_apply, hεf, sub_self]
    have := Ideal.mem_map_of_mem (j : H →ₐ[𝓞] L) h1f
    rwa [map_sub, map_one] at this

  have hf0 : f ≠ 0 := fun h => by
    rw [h, map_zero] at hεf
    exact zero_ne_one hεf
  have hItop : I ≠ ⊤ := fun h => by
    have h1 : (1 : H) ∈ I := h ▸ Submodule.mem_top
    rw [hIdef, mem_span_one_sub_iff hf, one_mul] at h1
    exact hf0 h1
  haveI : Nontrivial (H ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
  have hjf : IsIdempotentElem (j f) := hf.map (j : H →ₐ[𝓞] L)
  have hcomap : Ideal.comap (j : H →+* L) (Ideal.span {1 - j f}) ≤ I := by
    intro h hh
    rw [Ideal.mem_comap, mem_span_one_sub_iff hjf] at hh
    rw [hIdef, mem_span_one_sub_iff hf]
    apply hj
    change (j : H →+* L) (h * f) = j 0
    rw [map_mul, map_zero]
    exact hh
  have hIle : I ≤ Ideal.comap (j : H →+* L) (Ideal.span {1 - j f}) := by
    rw [hIdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    change (j : H →+* L) (1 - f) ∈ Ideal.span {1 - j f}
    rw [map_sub, map_one]
    exact Ideal.mem_span_singleton_self _
  let q : H ⧸ I →+* L ⧸ Ideal.span {1 - j f} := Ideal.quotientMap _ (j : H →+* L) hIle
  have hq : Function.Injective q := Ideal.quotientMap_injective' hcomap
  haveI := hloc
  have hidem : ∀ u : H ⧸ I, IsIdempotentElem u → u = 0 ∨ u = 1 := by
    intro u hu
    rcases eq_zero_or_one_of_isLocalRing (hu.map q) with h0 | h1
    · left; apply hq; rw [h0, map_zero]
    · right; apply hq; rw [h1, map_one]
  haveI : IsLocalRing (H ⧸ I) := isLocalRing_of_forall_isIdempotentElem (𝓞 := 𝓞) hidem

  set K := ZMod p ⊗[𝓞] (H ⧸ I) with hKdef
  have hKred : IsReduced K := by
    let φ : ZMod p ⊗[𝓞] H →ₐ[𝓞] K :=
      Algebra.TensorProduct.map (AlgHom.id 𝓞 (ZMod p)) (Ideal.Quotient.mkₐ 𝓞 I)
    have hφs : Function.Surjective φ := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul c y =>
        obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨c ⊗ₜ h, by rw [Algebra.TensorProduct.map_tmul]; rfl⟩
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    have hφk : RingHom.ker φ = Ideal.span {1 - (1 : ZMod p) ⊗ₜ[𝓞] f} := by
      change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id 𝓞 (ZMod p)) (Ideal.Quotient.mkₐ 𝓞 I)) = _
      rw [Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective 𝓞 I)]
      have hk' : RingHom.ker (Ideal.Quotient.mkₐ 𝓞 I) = I := Ideal.mk_ker
      rw [hk', hIdef, Ideal.map_span, Set.image_singleton]
      simp only [map_sub, map_one, Algebra.TensorProduct.includeRight_apply]
    have he : IsIdempotentElem ((1 : ZMod p) ⊗ₜ[𝓞] f) := by
      change (1 : ZMod p) ⊗ₜ[𝓞] f * (1 : ZMod p) ⊗ₜ[𝓞] f = (1 : ZMod p) ⊗ₜ[𝓞] f
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hf.eq]
    haveI := hred
    haveI : IsReduced ((ZMod p ⊗[𝓞] H) ⧸ RingHom.ker φ) := by
      rw [hφk]; exact isReduced_quotient_span_one_sub he
    let e := Ideal.quotientKerAlgEquivOfSurjective hφs
    exact isReduced_of_injective e.symm.toRingEquiv.toRingHom e.symm.injective

  have hpJ : Ideal.span {(p : 𝓞)} ≤ (⊥ : Ideal 𝓞).jacobson := IsAdicComplete.le_jacobson_bot _
  haveI : Nontrivial K := by
    by_contra hK
    rw [not_nontrivial_iff_subsingleton] at hK
    have htop : (⊤ : Submodule 𝓞 (H ⧸ I)) ≤ Ideal.span {(p : 𝓞)} • ⊤ := by
      intro y _
      have hy : y ∈ RingHom.ker (red 𝓞 p (H ⧸ I) : H ⧸ I →ₐ[𝓞] K) := Subsingleton.elim _ _
      rw [ker_red hk hker] at hy
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      rw [mul_comm, ← map_natCast (algebraMap 𝓞 (H ⧸ I)), ← Algebra.smul_def]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(p : 𝓞)}) ⊤ Module.Finite.fg_top htop hpJ
    exact zero_ne_one ((Submodule.eq_bot_iff _).1 this 1 Submodule.mem_top).symm
  haveI : IsLocalRing K := IsLocalRing.of_surjective' (red 𝓞 p (H ⧸ I)).toRingHom (red_surjective hk)
  haveI : IsArtinianRing K := IsArtinianRing.of_finite (ZMod p) K
  have hKfield : IsField K := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := K)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    have : x ^ n = 0 := by
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      exact (Submodule.mem_bot _).1 this
    exact (Submodule.mem_bot _).2 (hKred.eq_zero x ⟨n, this⟩)

  let εf : H ⧸ I →ₐ[𝓞] 𝓞 := Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom 𝓞 H) fun a ha => by
    rw [hIdef] at ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    change Bialgebra.counitAlgHom 𝓞 H (b * (1 - f)) = 0
    rw [map_mul, map_sub, map_one]
    simp only [Bialgebra.counitAlgHom_apply]
    rw [hεf, sub_self, mul_zero]
  let θ : K →ₐ[ZMod p] ZMod p :=
    (Algebra.TensorProduct.rid 𝓞 (ZMod p) (ZMod p)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) εf)
  have hθ : Function.Injective θ := by
    letI := hKfield.toField
    exact (θ : K →+* ZMod p).injective
  have hK : ∀ k : K, k = algebraMap (ZMod p) K (θ k) := by
    intro k
    apply hθ
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

  have hlift : ∀ y : H ⧸ I, ∃ c : 𝓞, y - algebraMap 𝓞 (H ⧸ I) c ∈ Ideal.span {(p : H ⧸ I)} := by
    intro y
    obtain ⟨c, hc⟩ := hk (θ (red 𝓞 p (H ⧸ I) y))
    refine ⟨c, ?_⟩
    rw [← ker_red hk hker, RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, hc]
    conv_lhs => rw [hK (red 𝓞 p (H ⧸ I) y)]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hall : ∀ y : H ⧸ I, ∃ c : 𝓞, y = algebraMap 𝓞 (H ⧸ I) c := by
    have hN : (⊤ : Submodule 𝓞 (H ⧸ I)) ≤ LinearMap.range (Algebra.linearMap 𝓞 (H ⧸ I)) := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hpJ ?_
      intro y _
      obtain ⟨c, hc⟩ := hlift y
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hc
      have hy : y = algebraMap 𝓞 (H ⧸ I) c + (p : 𝓞) • d := by
        rw [Algebra.smul_def, map_natCast]
        linear_combination (-1 : H ⧸ I) * hd
      rw [hy]
      exact Submodule.add_mem_sup ⟨c, rfl⟩
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
    intro y
    obtain ⟨c, hc⟩ := hN (Submodule.mem_top (x := y))
    exact ⟨c, hc.symm⟩

  rw [Ideal.map_le_iff_le_comap]
  intro h hh
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hh
  obtain ⟨c, hc⟩ := hall (Ideal.Quotient.mk I h)
  have hc0 : c = 0 := by
    have := congrArg εf hc
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
    rw [← this]
    change Ideal.Quotient.lift I ((Bialgebra.counitAlgHom 𝓞 H : H →+* 𝓞)) _ (Ideal.Quotient.mk I h) = 0
    rw [Ideal.Quotient.lift_mk]
    exact hh
  rw [hc0, map_zero, Ideal.Quotient.eq_zero_iff_mem, hIdef] at hc
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hc
  rw [Ideal.mem_comap, ← hb]
  change (j : H →+* L) (b * (1 - f)) ∈ Ideal.span {1 - j f}
  rw [map_mul, map_sub, map_one]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end S_HopfAlgebra_map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp
end P2MW
export P2MW.S_HopfAlgebra_map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp (solution)
