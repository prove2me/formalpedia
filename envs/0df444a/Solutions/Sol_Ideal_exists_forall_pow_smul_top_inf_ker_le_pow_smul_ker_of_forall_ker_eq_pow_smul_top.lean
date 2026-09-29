-- Prove2me | solution 1 for Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e2b55ea6-7420-51b9-97eb-4c35c79e09be

import Mathlib
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

universe u v w

open Submodule

namespace P2mAdicKerAR

section Filtration

variable {B : Type u} [CommRing B] (J : Ideal B) {E : Type v} [AddCommGroup E] [Module B E]
  (Msub : ℕ → Submodule B E)

def Mhat : Submodule (AdicCompletion J B) (AdicCompletion J E) where
  carrier := {x | ∀ j : ℕ, x.val (j + 1) ∈ (Msub j).map (mkQ (J ^ (j + 1) • ⊤ : Submodule B E))}
  zero_mem' j := by
    rw [AdicCompletion.val_zero_apply]
    exact zero_mem _
  add_mem' {x y} hx hy j := by
    rw [AdicCompletion.val_add_apply]
    exact add_mem (hx j) (hy j)
  smul_mem' r x hx j := by
    rw [AdicCompletion.smul_eval]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (r.val (j + 1))
    obtain ⟨y, hy, hyx⟩ := hx j
    rw [← hb, ← hyx, mkQ_apply, AdicCompletion.mk_smul_mk, ← Submodule.Quotient.mk_smul]
    exact ⟨b • y, (Msub j).smul_mem b hy, rfl⟩

theorem mem_Mhat_iff (x : AdicCompletion J E) :
    x ∈ Mhat J Msub ↔ ∀ j : ℕ, x.val (j + 1) ∈ (Msub j).map (mkQ (J ^ (j + 1) • ⊤ : Submodule B E)) :=
  Iff.rfl

variable {J Msub}

theorem exists_mem_succ_sub_mem (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤)
    (k : ℕ) (y : E) (hy : y ∈ Msub k) :
    ∃ y' ∈ Msub (k + 1), y - y' ∈ (J ^ (k + 1) • ⊤ : Submodule B E) := by
  obtain ⟨y', hy', z, hz, hyz⟩ := Submodule.mem_sup.mp (hstep k hy)
  exact ⟨y', hy', by rw [← hyz, add_sub_cancel_left]; exact hz⟩

noncomputable def tseq (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) : ∀ i : ℕ, {y : E // y ∈ Msub (n + i)}
  | 0 => ⟨x, hx⟩
  | i + 1 =>
    ⟨Classical.choose (exists_mem_succ_sub_mem hstep (n + i) (tseq hstep n x hx i).1 (tseq hstep n x hx i).2),
      (Classical.choose_spec
        (exists_mem_succ_sub_mem hstep (n + i) (tseq hstep n x hx i).1 (tseq hstep n x hx i).2)).1⟩

theorem tseq_zero (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) : (tseq hstep n x hx 0).1 = x := rfl

theorem tseq_sub_succ_mem (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) (i : ℕ) :
    (tseq hstep n x hx i).1 - (tseq hstep n x hx (i + 1)).1 ∈ (J ^ (n + i + 1) • ⊤ : Submodule B E) :=
  (Classical.choose_spec
    (exists_mem_succ_sub_mem hstep (n + i) (tseq hstep n x hx i).1 (tseq hstep n x hx i).2)).2

noncomputable def cseq (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) : AdicCompletion.AdicCauchySequence J E :=
  AdicCompletion.AdicCauchySequence.mk J E (fun m => (tseq hstep n x hx (m - n)).1) (by
    intro m
    have hcongr : ∀ a b : ℕ, a = b → (tseq hstep n x hx a).1 = (tseq hstep n x hx b).1 := by
      rintro a _ rfl; rfl
    rw [SModEq.sub_mem]
    show (tseq hstep n x hx (m - n)).1 - (tseq hstep n x hx (m + 1 - n)).1 ∈ (J ^ m • ⊤ : Submodule B E)
    by_cases hm : m < n
    · rw [hcongr (m - n) 0 (by omega), hcongr (m + 1 - n) 0 (by omega), sub_self]
      exact zero_mem _
    · rw [hcongr (m + 1 - n) (m - n + 1) (by omega)]
      have hle : J ^ (n + (m - n) + 1) ≤ J ^ m := Ideal.pow_le_pow_right (by omega)
      exact Submodule.smul_mono_left hle (tseq_sub_succ_mem hstep n x hx (m - n)))

theorem cseq_apply (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) (m : ℕ) : cseq hstep n x hx m = (tseq hstep n x hx (m - n)).1 := rfl

noncomputable def xhat (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) : AdicCompletion J E :=
  AdicCompletion.mk J E (cseq hstep n x hx)

theorem xhat_val (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) (m : ℕ) :
    (xhat hstep n x hx).val m = mkQ (J ^ m • ⊤ : Submodule B E) (tseq hstep n x hx (m - n)).1 := rfl

theorem Msub_le_of_le (hanti : ∀ k, Msub (k + 1) ≤ Msub k) {i j : ℕ} (hij : i ≤ j) : Msub j ≤ Msub i := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact (hanti _).trans ih

theorem xhat_mem_Mhat (hanti : ∀ k, Msub (k + 1) ≤ Msub k)
    (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E) (hx : x ∈ Msub n) :
    xhat hstep n x hx ∈ Mhat J Msub := by
  intro j
  rw [xhat_val]
  refine ⟨(tseq hstep n x hx (j + 1 - n)).1, ?_, rfl⟩
  have hle : j ≤ n + (j + 1 - n) := by omega
  exact Msub_le_of_le hanti hle (tseq hstep n x hx (j + 1 - n)).2

theorem eval_xhat_eq_zero (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) (hxJ : x ∈ (J ^ n • ⊤ : Submodule B E)) :
    AdicCompletion.eval J E n (xhat hstep n x hx) = 0 := by
  rw [AdicCompletion.eval_apply]
  show (xhat hstep n x hx).val n = 0
  rw [xhat_val, Nat.sub_self, tseq_zero, mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hxJ

theorem eval_succ_xhat (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) (n : ℕ) (x : E)
    (hx : x ∈ Msub n) :
    AdicCompletion.eval J E (n + 1) (xhat hstep n x hx) = mkQ (J ^ (n + 1) • ⊤ : Submodule B E) x := by
  rw [AdicCompletion.eval_apply]
  show (xhat hstep n x hx).val (n + 1) = _
  rw [xhat_val, Nat.add_sub_cancel_left, mkQ_apply, mkQ_apply, eq_comm, Submodule.Quotient.eq]
  exact tseq_sub_succ_mem hstep n x hx 0

theorem map_eval_smul_Mhat_le (k n : ℕ) :
    (J ^ k • (Mhat J Msub).restrictScalars B).map (AdicCompletion.eval J E (n + 1)) ≤
      (J ^ k • Msub n).map (mkQ (J ^ (n + 1) • ⊤ : Submodule B E)) := by
  rw [Submodule.map_smul'', Submodule.map_smul'']
  refine Submodule.smul_mono le_rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hy n

variable (J Msub) in

theorem core [IsNoetherianRing B] [Module.Finite B E] (hanti : ∀ k, Msub (k + 1) ≤ Msub k)
    (hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • ⊤ : Submodule B E) ⊓ Msub n ≤ J ^ k • Msub n ⊔ J ^ (n + 1) • ⊤ := by

  haveI : IsNoetherianRing (AdicCompletion J B) := AdicCompletion.isNoetherianRing_of_isNoetherianRing J
  haveI : Module.Finite (AdicCompletion J B) (AdicCompletion J E) :=
    Module.Finite.of_surjective (AdicCompletion.ofTensorProduct J E)
      (AdicCompletion.ofTensorProduct_surjective_of_finite J E)
  have hJ : J.FG := (isNoetherianRing_iff_ideal_fg B).mp inferInstance J

  set Jh : Ideal (AdicCompletion J B) := J.map (algebraMap B (AdicCompletion J B)) with hJh
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul Jh (Mhat J Msub)
  refine ⟨c, fun k n hkn => ?_⟩
  rintro x ⟨hxJ, hx⟩
  have hxJ' : x ∈ (J ^ n • ⊤ : Submodule B E) := hxJ

  set xh := xhat hstep n x hx with hxh
  have h1 : xh ∈ (Jh ^ n • ⊤ : Submodule (AdicCompletion J B) (AdicCompletion J E)) := by
    have hker : xh ∈ LinearMap.ker (AdicCompletion.eval J E n) := by
      rw [LinearMap.mem_ker]; exact eval_xhat_eq_zero hstep n x hx hxJ'
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := E) hJ] at hker
    have : (Jh ^ n • ⊤ : Submodule (AdicCompletion J B) (AdicCompletion J E)).restrictScalars B =
        J ^ n • ⊤ := by
      rw [hJh, ← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    rw [← Submodule.restrictScalars_mem B, this]
    exact hker
  have h2 : xh ∈ Mhat J Msub := xhat_mem_Mhat hanti hstep n x hx
  have h3 : xh ∈ Jh ^ k • Mhat J Msub := by
    have hn : c ≤ n := le_trans (Nat.le_add_left c k) hkn
    have h12 : xh ∈ Jh ^ n • ⊤ ⊓ Mhat J Msub := ⟨h1, h2⟩
    rw [hc n hn] at h12
    have hle : Jh ^ (n - c) • (Jh ^ c • ⊤ ⊓ Mhat J Msub) ≤ Jh ^ k • Mhat J Msub :=
      (Submodule.smul_mono le_rfl inf_le_right).trans
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
    exact hle h12
  have h4 : xh ∈ J ^ k • (Mhat J Msub).restrictScalars B := by
    rw [← Ideal.smul_restrictScalars, Ideal.map_pow, ← hJh]
    exact h3

  have h5 : mkQ (J ^ (n + 1) • ⊤ : Submodule B E) x ∈
      (J ^ k • Msub n).map (mkQ (J ^ (n + 1) • ⊤ : Submodule B E)) := by
    rw [← eval_succ_xhat hstep n x hx]
    exact map_eval_smul_Mhat_le k n (Submodule.mem_map_of_mem h4)
  have h6 : x ∈ (J ^ k • Msub n) ⊔ (J ^ (n + 1) • ⊤ : Submodule B E) := by
    have := Submodule.mem_comap.mpr h5
    rwa [Submodule.comap_map_mkQ, sup_comm] at this
  exact h6

end Filtration

section System

variable {B : Type u} [CommRing B] (J : Ideal B)
  {G : ℕ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)]
  (γ : ∀ k, G (k + 1) →ₗ[B] G k)

theorem pow_succ_smul_top_eq_bot (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1)))) (k : ℕ) :
    J ^ (k + 1) • (⊤ : Submodule B (G k)) = ⊥ := by
  have h : (J ^ (k + 1) • (⊤ : Submodule B (G (k + 1)))).map (γ k) = J ^ (k + 1) • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hγs k)]
  rw [← h, ← hγk, eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot]

variable {E : Type w} [AddCommGroup E] [Module B E] [Module.Projective B E]

noncomputable def lifts (hγs : ∀ k, Function.Surjective (γ k)) (u0 : E →ₗ[B] G 0) : ∀ k : ℕ, E →ₗ[B] G k
  | 0 => u0
  | k + 1 => Classical.choose (Module.projective_lifting_property (γ k) (lifts hγs u0 k) (hγs k))

theorem comp_lifts_succ (hγs : ∀ k, Function.Surjective (γ k)) (u0 : E →ₗ[B] G 0) (k : ℕ) :
    γ k ∘ₗ lifts γ hγs u0 (k + 1) = lifts γ hγs u0 k :=
  Classical.choose_spec (Module.projective_lifting_property (γ k) (lifts γ hγs u0 k) (hγs k))

theorem lifts_zero (hγs : ∀ k, Function.Surjective (γ k)) (u0 : E →ₗ[B] G 0) : lifts γ hγs u0 0 = u0 := rfl

theorem eq_top_of_sup_smul_top {M : Type*} [AddCommGroup M] [Module B M] (I : Ideal B) (R : Submodule B M)
    (h : R ⊔ I • ⊤ = ⊤) (hI : (I * I) • (⊤ : Submodule B M) = ⊥) : R = ⊤ := by
  have h1 : I • (⊤ : Submodule B M) ≤ R := by
    calc I • (⊤ : Submodule B M) = I • (R ⊔ I • ⊤) := by rw [h]
      _ = I • R ⊔ (I * I) • ⊤ := by rw [Submodule.smul_sup, Submodule.mul_smul]
      _ ≤ R := by rw [hI, sup_bot_eq]; exact Submodule.smul_le_right
  rw [eq_top_iff, ← h]
  exact sup_le le_rfl h1

theorem lifts_surjective (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (u0 : E →ₗ[B] G 0) (hu0 : Function.Surjective u0) (k : ℕ) :
    Function.Surjective (lifts γ hγs u0 k) := by
  induction k with
  | zero => exact hu0
  | succ k ih =>
    rw [← LinearMap.range_eq_top]
    apply eq_top_of_sup_smul_top (J ^ (k + 1)) (LinearMap.range (lifts γ hγs u0 (k + 1)))
    ·
      rw [eq_top_iff]
      intro g _
      obtain ⟨e, he⟩ := ih (γ k g)
      rw [← comp_lifts_succ γ hγs u0 k, LinearMap.comp_apply] at he
      have hmem : g - lifts γ hγs u0 (k + 1) e ∈ LinearMap.ker (γ k) := by
        rw [LinearMap.mem_ker, map_sub, he, sub_self]
      rw [hγk] at hmem
      have : g = lifts γ hγs u0 (k + 1) e + (g - lifts γ hγs u0 (k + 1) e) := by abel
      rw [this]
      exact Submodule.add_mem_sup ⟨e, rfl⟩ hmem
    · rw [← pow_add]
      have hle : J ^ (k + 1 + (k + 1)) ≤ J ^ (k + 1 + 1) := Ideal.pow_le_pow_right (by omega)
      exact eq_bot_iff.mpr ((Submodule.smul_mono_left hle).trans
        (pow_succ_smul_top_eq_bot J γ hγs hγk (k + 1)).le)

end System

section Kernel

variable {B : Type u} [CommRing B] (J : Ideal B)
  {G : ℕ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)]
  {F : ℕ → Type w} [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
  (γ : ∀ k, G (k + 1) →ₗ[B] G k) (φ : ∀ k, F (k + 1) →ₗ[B] F k) (θ : ∀ k, G k →ₗ[B] F k)
  {E : Type*} [AddCommGroup E] [Module B E]

theorem comap_ker_succ_le (u : ∀ k, E →ₗ[B] G k) (hu : ∀ k, γ k ∘ₗ u (k + 1) = u k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) (k : ℕ) :
    (LinearMap.ker (θ (k + 1))).comap (u (k + 1)) ≤ (LinearMap.ker (θ k)).comap (u k) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mem_ker] at hy ⊢
  rw [← hu k, LinearMap.comp_apply, ← LinearMap.comp_apply (θ k), ← hθc k, LinearMap.comp_apply, hy, map_zero]

theorem comap_ker_le_succ_sup (u : ∀ k, E →ₗ[B] G k) (hu : ∀ k, γ k ∘ₗ u (k + 1) = u k)
    (hus : ∀ k, Function.Surjective (u k)) (hθs : ∀ k, Function.Surjective (θ k))
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) (k : ℕ) :
    (LinearMap.ker (θ k)).comap (u k) ≤
      (LinearMap.ker (θ (k + 1))).comap (u (k + 1)) ⊔ J ^ (k + 1) • (⊤ : Submodule B E) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mem_ker] at hy
  have h1 : θ (k + 1) (u (k + 1) y) ∈ LinearMap.ker (φ k) := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hθc k, LinearMap.comp_apply, ← LinearMap.comp_apply (γ k),
      hu k, hy]
  replace h1 := hφk k h1
  have hsurj : Function.Surjective (θ (k + 1) ∘ₗ u (k + 1)) := (hθs (k + 1)).comp (hus (k + 1))
  have h2 : (J ^ (k + 1) • (⊤ : Submodule B (F (k + 1)))) =
      (J ^ (k + 1) • (⊤ : Submodule B E)).map (θ (k + 1) ∘ₗ u (k + 1)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  rw [h2] at h1
  obtain ⟨z, hz, hzy⟩ := h1
  rw [Submodule.mem_sup]
  refine ⟨y - z, ?_, z, hz, sub_add_cancel y z⟩
  rw [Submodule.mem_comap, LinearMap.mem_ker, map_sub, map_sub]
  rw [LinearMap.comp_apply] at hzy
  rw [hzy, sub_self]

theorem map_inf_map_le {M' : Type*} [AddCommGroup M'] [Module B M'] (f : E →ₗ[B] M') (A M : Submodule B E)
    (hM : LinearMap.ker f ≤ M) : A.map f ⊓ M.map f ≤ (A ⊓ M).map f := by
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨m, hm, hma⟩⟩
  have : a - m ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, map_sub, hma, sub_self]
  have ha' : a ∈ M := by
    have := M.add_mem (hM this) hm
    rwa [sub_add_cancel] at this
  exact ⟨a, ⟨ha, ha'⟩, rfl⟩

end Kernel

theorem main {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) := by

  obtain ⟨m, u0, hu0⟩ := Module.Finite.exists_fin' B (G 0)
  let u : ∀ k, (Fin m → B) →ₗ[B] G k := lifts γ hγs u0
  have hu : ∀ k, γ k ∘ₗ u (k + 1) = u k := comp_lifts_succ γ hγs u0
  have hus : ∀ k, Function.Surjective (u k) := lifts_surjective J γ hγs hγk u0 hu0

  let Msub : ℕ → Submodule B (Fin m → B) := fun k => (LinearMap.ker (θ k)).comap (u k)
  have hanti : ∀ k, Msub (k + 1) ≤ Msub k := comap_ker_succ_le γ φ θ u hu hθc
  have hstep : ∀ k, Msub k ≤ Msub (k + 1) ⊔ J ^ (k + 1) • ⊤ :=
    comap_ker_le_succ_sup J γ φ θ u hu hus hθs hφk hθc
  obtain ⟨c, hc⟩ := core J Msub hanti hstep
  refine ⟨c, fun k n hkn => ?_⟩

  have hL : LinearMap.ker (θ n) = (Msub n).map (u n) := (Submodule.map_comap_eq_of_surjective (hus n) _).symm
  have hA : (J ^ n • (⊤ : Submodule B (G n))) = (J ^ n • (⊤ : Submodule B (Fin m → B))).map (u n) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hus n)]
  have hker : LinearMap.ker (u n) ≤ Msub n := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    show y ∈ (LinearMap.ker (θ n)).comap (u n)
    rw [Submodule.mem_comap, hy]; exact zero_mem _
  have hann : J ^ (n + 1) • (⊤ : Submodule B (G n)) = ⊥ := pow_succ_smul_top_eq_bot J γ hγs hγk n
  calc (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n)
      = (J ^ n • (⊤ : Submodule B (Fin m → B))).map (u n) ⊓ (Msub n).map (u n) := by rw [hA, hL]
    _ ≤ ((J ^ n • ⊤) ⊓ Msub n).map (u n) := map_inf_map_le (u n) _ _ hker
    _ ≤ (J ^ k • Msub n ⊔ J ^ (n + 1) • ⊤).map (u n) := Submodule.map_mono (hc k n hkn)
    _ = J ^ k • LinearMap.ker (θ n) := by
        rw [Submodule.map_sup, Submodule.map_smul'', ← hL, Submodule.map_smul'', Submodule.map_top,
          LinearMap.range_eq_top.mpr (hus n), hann, sup_bot_eq]

end P2mAdicKerAR

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) :=
  P2mAdicKerAR.main J G F γ hγs hγk φ hφk θ hθs hθc

end S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top (solution)
