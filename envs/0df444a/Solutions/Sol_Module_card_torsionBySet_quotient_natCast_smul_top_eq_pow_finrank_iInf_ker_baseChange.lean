-- Prove2me | solution 1 for Module.card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/194875fb-8b08-5af1-a258-b92da909edcd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange

open scoped TensorProduct

namespace G3Aux

open Submodule

open Submodule

theorem exists_finset_iInf_eq {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsArtinian R M]
    {ι : Type*} (S : ι → Submodule R M) : ∃ s : Finset ι, ⨅ i, S i = ⨅ i ∈ s, S i := by
  classical
  obtain ⟨m, ⟨s₀, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (R := R) (M := M)
    (Set.range fun s : Finset ι => ⨅ i ∈ s, S i) ⟨_, ∅, rfl⟩
  refine ⟨s₀, le_antisymm (le_iInf₂ fun i _ => iInf_le S i) (le_iInf fun j => ?_)⟩
  have hle : (⨅ i ∈ insert j s₀, S i) ≤ ⨅ i ∈ s₀, S i :=
    biInf_mono fun i hi => Finset.mem_insert_of_mem hi
  have hnlt : ¬ (⨅ i ∈ insert j s₀, S i) < ⨅ i ∈ s₀, S i := hmin _ ⟨insert j s₀, rfl⟩
  have heq : (⨅ i ∈ insert j s₀, S i) = ⨅ i ∈ s₀, S i := (eq_or_lt_of_le hle).resolve_right hnlt
  rw [← heq]
  exact biInf_le _ (Finset.mem_insert_self j s₀)

theorem baseChange_le_ker {F : Type*} [CommRing F] (K : Type*) [CommRing K] [Algebra F K]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) : (LinearMap.ker f).baseChange K ≤ LinearMap.ker (f.baseChange K) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
  rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hw, TensorProduct.tmul_zero]

theorem finrank_iInf_ker_baseChange_eq
    (F : Type) [Field F] (K : Type) [Field K] [Algebra F K]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type} (T : ι → (V →ₗ[F] V)) :
    Module.finrank K ↥(⨅ i, LinearMap.ker ((T i).baseChange K)) =
      Module.finrank F ↥(⨅ i, LinearMap.ker (T i)) := by
  classical
  set W : Submodule F V := ⨅ i, LinearMap.ker (T i) with hW

  have key : (⨅ i, LinearMap.ker ((T i).baseChange K)) = W.baseChange K := by
    apply le_antisymm
    ·
      haveI : IsArtinian F V := inferInstance
      obtain ⟨s, hs⟩ := exists_finset_iInf_eq (fun i => LinearMap.ker (T i))

      let Φ : V →ₗ[F] (↥s → V) := LinearMap.pi fun i : ↥s => T (i : ι)
      have hkerΦ : LinearMap.ker Φ = W := by
        rw [hW, hs, LinearMap.ker_pi]
        ext v
        simp only [Submodule.mem_iInf]
        exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

      let Φbar : (V ⧸ W) →ₗ[F] (↥s → V) := W.liftQ Φ hkerΦ.ge
      have hΦbar : LinearMap.ker Φbar = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hkerΦ.le
      obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φbar hΦbar
      have hinjK : Function.Injective (Φbar.baseChange K) := by
        intro a b hab
        have := congrArg (Ψ.baseChange K) hab
        rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hΨ,
          LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this

      have hex : Function.Exact (W.subtype.baseChange K) (W.mkQ.baseChange K) := by
        have h := lTensor_exact K (LinearMap.exact_subtype_mkQ W) (Submodule.mkQ_surjective W)
        intro x
        have hx := h x
        simp only [← LinearMap.baseChange_eq_ltensor] at hx
        rw [hx]
      intro x hx

      have h0 : (W.mkQ.baseChange K) x = 0 := by
        apply hinjK
        rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, Submodule.liftQ_mkQ]

        apply (TensorProduct.piRight F K K (fun _ : ↥s => V)).injective
        rw [map_zero]
        funext i
        have hcomp : ∀ y : K ⊗[F] V, TensorProduct.piRight F K K (fun _ : ↥s => V) (Φ.baseChange K y) i
            = (T (i : ι)).baseChange K y := by
          intro y
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul k v => simp [Φ]
          | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
        rw [hcomp, Pi.zero_apply]
        exact (Submodule.mem_iInf _).mp hx (i : ι)
      obtain ⟨y, hy⟩ := (hex x).mp h0
      exact ⟨y, hy⟩
    · rw [hW]
      refine le_iInf fun i => (Submodule.baseChange_mono _ (iInf_le _ i)).trans ?_
      exact baseChange_le_ker K (T i)
  rw [key]

  rw [← (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq, Module.finrank_baseChange]

theorem finrank_iInf_ker_eq_of_linearEquiv {k : Type*} [Field k] {X Y : Type*}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] (E : X ≃ₗ[k] Y)
    {ι : Type*} (f : ι → (X →ₗ[k] X)) (g : ι → (Y →ₗ[k] Y))
    (h : ∀ i x, E (f i x) = g i (E x)) :
    Module.finrank k ↥(⨅ i, LinearMap.ker (f i)) = Module.finrank k ↥(⨅ i, LinearMap.ker (g i)) := by
  have hmap : (⨅ i, LinearMap.ker (g i)).comap (E : X →ₗ[k] Y) = ⨅ i, LinearMap.ker (f i) := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · intro hx i
      apply E.injective
      rw [h, hx i, map_zero]
    · intro hx i
      rw [← h, hx i, map_zero]
  rw [← hmap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem key (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    {M : Type} [AddCommGroup M] (V : Type) [AddCommGroup V] [instV : Module (ZMod p) V]
    [finV : Module.Finite (ZMod p) V]
    (π : M →ₗ[ℤ] V) (hπ : Function.Bijective (π.baseChange k))
    {ι : Type} (f : ι → (M →ₗ[ℤ] M)) (g : ι → (V →ₗ[ZMod p] V))
    (hfg : ∀ i m, π (f i m) = g i (π m))
    (N : Set V) (hN : ∀ v, v ∈ N ↔ ∀ i, g i v = 0) :
    Nat.card N = p ^ Module.finrank k ↥(⨅ i, LinearMap.ker ((f i).baseChange k)) := by
  have hcard : Nat.card N = Nat.card ↥(⨅ i, LinearMap.ker (g i)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [hN v, Submodule.mem_iInf]
    exact forall_congr' fun i => LinearMap.mem_ker.symm
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  congr 1
  symm
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let E₁ : k ⊗[ℤ] M ≃ₗ[k] k ⊗[ℤ] V := LinearEquiv.ofBijective (π.baseChange k) hπ
  haveI : TensorProduct.CompatibleSMul ℤ (ZMod p) k V :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective (R := ℤ) (A := ZMod p) (M := k) (N := V)
      ZMod.intCast_surjective
  let E₂ := (TensorProduct.equivOfCompatibleSMul ℤ (ZMod p) k k V).symm
  let E := E₁.trans E₂
  have hE₂ : ∀ (c : k) (v : V), E₂ (c ⊗ₜ[ℤ] v) = c ⊗ₜ[ZMod p] v := by
    intro c v
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hE : ∀ (c : k) (m : M), E (c ⊗ₜ[ℤ] m) = c ⊗ₜ[ZMod p] π m := by
    intro c m
    show E₂ (E₁ (c ⊗ₜ[ℤ] m)) = _
    rw [← hE₂]
    rfl
  rw [← finrank_iInf_ker_baseChange_eq (ZMod p) k V g]
  refine finrank_iInf_ker_eq_of_linearEquiv E (fun i => (f i).baseChange k)
    (fun i => (g i).baseChange k) ?_
  intro i x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m => rw [LinearMap.baseChange_tmul, hE, hE, LinearMap.baseChange_tmul, hfg]
  | add a b ha hb =>
    simp only [map_add] at ha hb ⊢
    rw [ha, hb]

end G3Aux

open G3Aux in
theorem solution
    (T : Type) [CommRing T] (M : Type) [AddCommGroup M] [Module T M] [Module.Finite ℤ M]
    (𝔪 : Ideal T) (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    Nat.card ↥(Submodule.torsionBySet T (M ⧸ (Ideal.span {((p : ℕ) : T)} • (⊤ : Submodule T M))) 𝔪) =
      p ^ Module.finrank k ↥(⨅ (t : T) (_ : t ∈ 𝔪),
        LinearMap.ker ((DistribSMul.toLinearMap ℤ M t).baseChange k)) := by
  classical

  set S : Submodule T M := Ideal.span {((p : ℕ) : T)} • (⊤ : Submodule T M) with hS

  have hSmem : ∀ s ∈ S, ∃ m : M, s = (p : ℕ) • m := by
    intro s hs
    rw [hS, Submodule.ideal_span_singleton_smul] at hs
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hs
    exact ⟨m, by rw [Nat.cast_smul_eq_nsmul]⟩

  have hpV : ∀ v : M ⧸ S, p • v = 0 := by
    intro v
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective S v
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul T, hS]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI instZ : Module (ZMod p) (M ⧸ S) := AddCommMonoid.zmodModule hpV

  let π : M →ₗ[ℤ] (M ⧸ S) := S.mkQ.toAddMonoidHom.toIntLinearMap
  have hπ : ∀ m : M, π m = Submodule.Quotient.mk m := fun _ => rfl
  have hπsurj : Function.Surjective π := Submodule.mkQ_surjective S
  haveI : Module.Finite ℤ (M ⧸ S) := Module.Finite.of_surjective π hπsurj
  haveI finZ : Module.Finite (ZMod p) (M ⧸ S) := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) (M ⧸ S)
  have hexact : Function.Exact (S.restrictScalars ℤ).subtype π := by
    intro m
    rw [hπ, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm; exact ⟨⟨m, hm⟩, rfl⟩
    · rintro ⟨x, rfl⟩; exact x.2
  have hzero : ∀ y, ((S.restrictScalars ℤ).subtype.baseChange k) y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c s =>
      obtain ⟨m, hm⟩ := hSmem s s.2
      rw [LinearMap.baseChange_tmul]
      show c ⊗ₜ[ℤ] (s : M) = 0
      rw [hm, ← natCast_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast,
        CharP.cast_eq_zero, zero_mul, TensorProduct.zero_tmul]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
  have hinj : Function.Injective (π.baseChange k) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h := lTensor_exact k hexact hπsurj x
    simp only [← LinearMap.baseChange_eq_ltensor] at h
    obtain ⟨y, rfl⟩ := h.mp hx
    rw [Submodule.mem_bot]
    exact hzero y

  let g : ↥𝔪 → ((M ⧸ S) →ₗ[ZMod p] (M ⧸ S)) := fun t =>
    (DistribSMul.toAddMonoidHom (M ⧸ S) (t : T)).toZModLinearMap p

  rw [iInf_subtype']
  exact key p k (M ⧸ S) (instV := instZ) (finV := finZ) π ⟨hinj, LinearMap.baseChange_surjective k hπsurj⟩
    (fun t : ↥𝔪 => DistribSMul.toLinearMap ℤ M (t : T)) g (fun t m => rfl)
    (Submodule.torsionBySet T (M ⧸ S) (𝔪 : Set T) : Set (M ⧸ S))
    (fun v => (Submodule.mem_torsionBySet_iff _ _).trans (forall_congr' fun t => Iff.rfl))

end S_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange
end P2MW
export P2MW.S_Module_card_torsionBySet_quotient_natCast_smul_top_eq_pow_finrank_iInf_ker_baseChange (solution)
