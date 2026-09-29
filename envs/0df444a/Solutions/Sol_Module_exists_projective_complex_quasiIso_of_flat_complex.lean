-- Prove2me | solution 1 for Module.exists_projective_complex_quasiIso_of_flat_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7f374b3f-60a7-5c2c-b23a-0a98f5e7618a

import Mathlib
import Theorems.Thm_Module_Flat_ker_of_surjective_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_projective_complex_quasiIso_of_flat_complex

set_option autoImplicit false

universe u

open TensorProduct

namespace MumfordModel

variable {R : Type u} [CommRing R]

def W (R : Type u) [CommRing R] (m : ℕ) : Submodule R (ℕ → R) where
  carrier := {f | ∀ k, m ≤ k → f k = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {f g} hf hg k hk => by
    show f k + g k = 0
    rw [hf k hk, hg k hk, add_zero]
  smul_mem' := fun a f hf k hk => by
    show a * f k = 0
    rw [hf k hk, mul_zero]

theorem mem_W {m : ℕ} {f : ℕ → R} : f ∈ W R m ↔ ∀ k, m ≤ k → f k = 0 := Iff.rfl

def πv (m : ℕ) : (ℕ → R) →ₗ[R] (Fin m → R) := LinearMap.funLeft R R (Fin.val : Fin m → ℕ)

theorem πv_apply (m : ℕ) (f : ℕ → R) (k : Fin m) : πv m f k = f k := rfl

def ιv (m : ℕ) : (Fin m → R) →ₗ[R] (ℕ → R) :=
  LinearMap.pi fun k => if h : k < m then LinearMap.proj (⟨k, h⟩ : Fin m) else 0

theorem ιv_apply (m : ℕ) (v : Fin m → R) (k : ℕ) :
    ιv m v k = if h : k < m then v ⟨k, h⟩ else 0 := by
  unfold ιv
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem ιv_apply_lt (m : ℕ) (v : Fin m → R) (k : Fin m) : ιv m v k = v k := by
  rw [ιv_apply, dif_pos k.2]

theorem ιv_mem (m : ℕ) (v : Fin m → R) : ιv m v ∈ W R m := fun k hk => by
  rw [ιv_apply, dif_neg (not_lt.mpr hk)]

theorem πv_ιv (m : ℕ) (v : Fin m → R) : πv m (ιv m v) = v :=
  funext fun k => by rw [πv_apply, ιv_apply_lt]

theorem ιv_πv (m : ℕ) {f : ℕ → R} (hf : f ∈ W R m) : ιv m (πv m f) = f :=
  funext fun k => by
    rw [ιv_apply]
    split_ifs with h
    · rfl
    · exact (hf k (not_lt.mp h)).symm

theorem ιv_injective (m : ℕ) : Function.Injective (ιv (R := R) m) :=
  fun v w h => by rw [← πv_ιv m v, ← πv_ιv m w, h]

theorem eq_zero_of_mem_W_zero {f : ℕ → R} (hf : f ∈ W R 0) : f = 0 :=
  funext fun k => hf k (Nat.zero_le k)

def lc {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ} (v : Fin r → M) : (Fin r → R) →ₗ[R] M :=
  ∑ k : Fin r, (LinearMap.proj k : (Fin r → R) →ₗ[R] R).smulRight (v k)

theorem lc_apply {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ} (v : Fin r → M) (a : Fin r → R) :
    lc v a = ∑ k : Fin r, a k • v k := by
  unfold lc
  rw [LinearMap.sum_apply]
  rfl

theorem lc_append_apply {M : Type u} [AddCommGroup M] [Module R M] {r s : ℕ} (v : Fin r → M) (w : Fin s → M)
    (a : Fin r → R) (b : Fin s → R) :
    lc (Fin.append v w) (Fin.append a b) = (∑ k : Fin r, a k • v k) + ∑ l : Fin s, b l • w l := by
  rw [lc_apply, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem map_lc {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {r : ℕ}
    (g : M →ₗ[R] N) (v : Fin r → M) (a : Fin r → R) : g (lc v a) = lc (fun k => g (v k)) a := by
  rw [lc_apply, lc_apply, map_sum]
  simp only [map_smul]

variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (n : ℕ)

structure Stage (b : ℕ) where
  m : ℕ → ℕ
  gδ : ℕ → ((ℕ → R) →ₗ[R] (ℕ → R))
  gφ : ∀ j, (ℕ → R) →ₗ[R] C j
  bdd : ∀ j, n < j → m j = 0
  maps : ∀ j, b ≤ j → ∀ f ∈ W R (m j), gδ j f ∈ W R (m (j + 1))
  dd : ∀ j, b ≤ j → ∀ f ∈ W R (m j), gδ (j + 1) (gδ j f) = 0
  chain : ∀ j, b ≤ j → ∀ f ∈ W R (m j), d j (gφ j f) = gφ (j + 1) (gδ j f)
  inj : ∀ j, b ≤ j → ∀ f ∈ W R (m (j + 1)), gδ (j + 1) f = 0 →
    gφ (j + 1) f ∈ LinearMap.range (d j) → ∃ g ∈ W R (m j), gδ j g = f
  surj : ∀ j, b ≤ j + 1 → ∀ y : C (j + 1), d (j + 1) y = 0 →
    ∃ f ∈ W R (m (j + 1)), gδ (j + 1) f = 0 ∧ gφ (j + 1) f - y ∈ LinearMap.range (d j)

variable {C d n}

def Stage.base (hbdd : ∀ i, n < i → Subsingleton (C i)) : Stage C d n (n + 1) where
  m := fun _ => 0
  gδ := fun _ => 0
  gφ := fun _ => 0
  bdd := fun _ _ => rfl
  maps := fun _ _ _ _ => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  dd := fun _ _ _ _ => by simp
  chain := fun _ _ _ _ => by simp
  inj := fun j _ f hf _ _ => ⟨0, Submodule.zero_mem _, by
    rw [LinearMap.zero_apply, eq_zero_of_mem_W_zero hf]⟩
  surj := fun j hj y _ => by
    haveI := hbdd (j + 1) (Nat.lt_of_succ_le hj)
    refine ⟨0, Submodule.zero_mem _, by rw [LinearMap.zero_apply], ?_⟩
    rw [LinearMap.zero_apply, Subsingleton.elim y 0, sub_zero]
    exact Submodule.zero_mem _

section Step

variable [IsNoetherianRing R]

theorem Stage.nonempty_step
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (p : ℕ) (hp : p < n) (S : Stage C d n (p + 1 + 1)) : Nonempty (Stage C d n (p + 1)) := by
  classical

  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℕ, m₂ = S.m (p + 1 + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Submodule R (Fin m₂ → R),
      B = (LinearMap.ker (S.gδ (p + 1 + 1)) ⊓
        (LinearMap.range (d (p + 1))).comap (S.gφ (p + 1 + 1))).comap (ιv m₂) := ⟨_, rfl⟩
  have hmemB : ∀ v : Fin m₂ → R, v ∈ B ↔ S.gδ (p + 1 + 1) (ιv m₂ v) = 0 ∧
      S.gφ (p + 1 + 1) (ιv m₂ v) ∈ LinearMap.range (d (p + 1)) := fun v => by
    rw [hB, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_comap]
  have hBfg : B.FG := IsNoetherian.noetherian B
  obtain ⟨r, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hBfg
  have hwB : ∀ k, w k ∈ B := fun k => hw ▸ Submodule.subset_span ⟨k, rfl⟩

  have hc : ∀ k, ∃ c : C (p + 1), d (p + 1) c = S.gφ (p + 1 + 1) (ιv m₂ (w k)) := fun k =>
    ((hmemB _).mp (hwB k)).2
  choose c hc using hc

  haveI := hfin p
  obtain ⟨s, qgen, hq⟩ := Module.Finite.exists_fin (R := R)
    (M := LinearMap.ker (d (p + 1)) ⧸ (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
  have hy : ∀ l, ∃ y : LinearMap.ker (d (p + 1)), Submodule.Quotient.mk y = qgen l :=
    fun l => Submodule.Quotient.mk_surjective _ (qgen l)
  choose ycyc hycyc using hy

  let newδ : (ℕ → R) →ₗ[R] (ℕ → R) :=
    ιv m₂ ∘ₗ lc (Fin.append w (fun _ : Fin s => (0 : Fin m₂ → R))) ∘ₗ πv (r + s)
  let newφ : (ℕ → R) →ₗ[R] C (p + 1) :=
    lc (Fin.append c (fun l => ((ycyc l : LinearMap.ker (d (p + 1))) : C (p + 1)))) ∘ₗ πv (r + s)
  have hlcB : ∀ a : Fin (r + s) → R, lc (Fin.append w (fun _ : Fin s => (0 : Fin m₂ → R))) a ∈ B := by
    intro a
    rw [lc_apply]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [Fin.append_left]; exact hwB i
    · rw [Fin.append_right]; exact Submodule.zero_mem _
  subst hm₂
  refine ⟨
    { m := Function.update S.m (p + 1) (r + s)
      gδ := Function.update S.gδ (p + 1) newδ
      gφ := Function.update S.gφ (p + 1) newφ
      bdd := ?_, maps := ?_, dd := ?_, chain := ?_, inj := ?_, surj := ?_ }⟩
  · intro j hj
    rw [Function.update_of_ne (by omega)]
    exact S.bdd j hj
  · intro j hj f hf
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rw [Function.update_self, Function.update_of_ne (by omega)]
      exact ιv_mem _ _
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [Function.update_of_ne (by omega)] at hf
      exact S.maps j (by omega) f hf
  · intro j hj f hf
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rw [Function.update_self, Function.update_of_ne (by omega)]
      show S.gδ (p + 1 + 1) (ιv _ (lc _ (πv (r + s) f))) = 0
      exact ((hmemB _).mp (hlcB _)).1
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rw [Function.update_of_ne (by omega)] at hf
      exact S.dd j (by omega) f hf
  · intro j hj f hf
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rw [Function.update_self, Function.update_self, Function.update_of_ne (by omega)]
      show d (p + 1) (lc _ (πv (r + s) f)) = S.gφ (p + 1 + 1) (ιv _ (lc _ (πv (r + s) f)))
      have hfun : (fun k => d (p + 1) (Fin.append c (fun l => ((ycyc l : LinearMap.ker (d (p + 1))) : C (p + 1))) k)) =
          (fun k => S.gφ (p + 1 + 1) (ιv _ (Fin.append w (fun _ : Fin s => (0 : Fin (S.m (p + 1 + 1)) → R)) k))) := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · simp only [Fin.append_left]; exact hc i
        · simp only [Fin.append_right, map_zero]
          exact LinearMap.mem_ker.mp (ycyc j).2
      rw [map_lc, map_lc, map_lc, hfun]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      rw [Function.update_of_ne (by omega)] at hf
      exact S.chain j (by omega) f hf
  · intro j hj f hf hδ hφ
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rw [Function.update_of_ne (by omega)] at hf hδ hφ
      rw [Function.update_self, Function.update_self]

      have hfB : πv (S.m (p + 1 + 1)) f ∈ B := by
        rw [hmemB, ιv_πv _ hf]
        exact ⟨hδ, hφ⟩
      rw [← hw, Submodule.mem_span_range_iff_exists_fun] at hfB
      obtain ⟨a, ha⟩ := hfB
      refine ⟨ιv (r + s) (Fin.append a 0), ιv_mem _ _, ?_⟩
      show ιv _ (lc _ (πv (r + s) (ιv (r + s) (Fin.append a 0)))) = f
      rw [πv_ιv, lc_append_apply]
      simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, add_zero]
      rw [ha, ιv_πv _ hf]
    · rw [Function.update_of_ne (by omega)] at hf hδ hφ
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact S.inj j (by omega) f hf hδ hφ
  · intro j hj y hy
    rcases Nat.eq_or_lt_of_le hj with hEq | hlt
    ·
      obtain rfl : p = j := by omega
      rw [Function.update_self, Function.update_self, Function.update_self]
      have htop : Submodule.Quotient.mk (p := (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
          (⟨y, LinearMap.mem_ker.mpr hy⟩ : LinearMap.ker (d (p + 1))) ∈
          Submodule.span R (Set.range qgen) := by
        rw [hq]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at htop
      obtain ⟨a, ha⟩ := htop
      refine ⟨ιv (r + s) (Fin.append 0 a), ιv_mem _ _, ?_, ?_⟩
      · show ιv _ (lc _ (πv (r + s) (ιv (r + s) (Fin.append 0 a)))) = 0
        rw [πv_ιv, lc_append_apply]
        simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, smul_zero, add_zero, map_zero]
      · show lc _ (πv (r + s) (ιv (r + s) (Fin.append 0 a))) - y ∈ LinearMap.range (d p)
        rw [πv_ιv, lc_append_apply]
        simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
        have hsum : (∑ l : Fin s, a l • qgen l) =
            ((LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype).mkQ
              (∑ l : Fin s, a l • (ycyc l : LinearMap.ker (d (p + 1)))) := by
          rw [map_sum]
          simp only [map_smul, Submodule.mkQ_apply, hycyc]
        rw [hsum, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap, map_sub] at ha
        simpa only [Submodule.coe_subtype, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk] using ha
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact S.surj j (by omega) y hy

end Step

theorem Stage.nonempty_descend [IsNoetherianRing R] (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    Nonempty (Stage C d n 1) :=
  Nat.decreasingInduction (motive := fun q _ => Nonempty (Stage C d n (q + 1)))
    (fun q hq h => h.elim fun S => Stage.nonempty_step hfin q hq S) ⟨Stage.base hbdd⟩ (Nat.zero_le n)

end MumfordModel

namespace MumfordModel

variable {R : Type u} [CommRing R]
variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  {d : ∀ i, C i →ₗ[R] C (i + 1)} {n : ℕ}

section Small

variable (S : Stage C d n 1)

abbrev Stage.K (i : ℕ) : Type u := Fin (S.m i) → R

def Stage.δs (i : ℕ) : S.K i →ₗ[R] S.K (i + 1) := πv (S.m (i + 1)) ∘ₗ S.gδ i ∘ₗ ιv (S.m i)

def Stage.φs (i : ℕ) : S.K i →ₗ[R] C i := S.gφ i ∘ₗ ιv (S.m i)

theorem Stage.δs_apply (i : ℕ) (v : S.K i) : S.δs i v = πv (S.m (i + 1)) (S.gδ i (ιv (S.m i) v)) := rfl

theorem Stage.φs_apply (i : ℕ) (v : S.K i) : S.φs i v = S.gφ i (ιv (S.m i) v) := rfl

theorem Stage.ιv_δs {i : ℕ} (hi : 1 ≤ i) (v : S.K i) :
    ιv (S.m (i + 1)) (S.δs i v) = S.gδ i (ιv (S.m i) v) := by
  rw [Stage.δs_apply, ιv_πv _ (S.maps i hi _ (ιv_mem _ _))]

theorem Stage.δs_δs {i : ℕ} (hi : 1 ≤ i) (v : S.K i) : S.δs (i + 1) (S.δs i v) = 0 := by
  rw [Stage.δs_apply, S.ιv_δs hi, S.dd i hi _ (ιv_mem _ _), map_zero]

theorem Stage.d_φs {i : ℕ} (hi : 1 ≤ i) (v : S.K i) : d i (S.φs i v) = S.φs (i + 1) (S.δs i v) := by
  rw [Stage.φs_apply, Stage.φs_apply, S.ιv_δs hi, S.chain i hi _ (ιv_mem _ _)]

theorem Stage.s_inj {i : ℕ} (hi : 1 ≤ i) (v : S.K (i + 1)) (hδ : S.δs (i + 1) v = 0)
    (hφ : S.φs (i + 1) v ∈ LinearMap.range (d i)) : ∃ w : S.K i, S.δs i w = v := by
  have h1 : S.gδ (i + 1) (ιv (S.m (i + 1)) v) = 0 := by
    rw [← S.ιv_δs (by omega) v, hδ, map_zero]
  obtain ⟨g, hg, hgv⟩ := S.inj i hi _ (ιv_mem _ _) h1 hφ
  refine ⟨πv (S.m i) g, ?_⟩
  rw [Stage.δs_apply, ιv_πv _ hg, hgv, πv_ιv]

theorem Stage.s_surj (i : ℕ) (y : C (i + 1)) (hy : d (i + 1) y = 0) :
    ∃ v : S.K (i + 1), S.δs (i + 1) v = 0 ∧ S.φs (i + 1) v - y ∈ LinearMap.range (d i) := by
  obtain ⟨f, hf, hδ, hφ⟩ := S.surj i (by omega) y hy
  refine ⟨πv (S.m (i + 1)) f, ?_, ?_⟩
  · rw [Stage.δs_apply, ιv_πv _ hf, hδ, map_zero]
  · rw [Stage.φs_apply, ιv_πv _ hf]; exact hφ

abbrev Stage.G (i : ℕ) : Type u := S.K (i + 1) × C i

def Stage.Δ (i : ℕ) : S.G i →ₗ[R] S.G (i + 1) :=
  (S.δs (i + 1) ∘ₗ LinearMap.fst R _ _).prod (S.φs (i + 1) ∘ₗ LinearMap.fst R _ _ - d i ∘ₗ LinearMap.snd R _ _)

theorem Stage.Δ_apply (i : ℕ) (v : S.K (i + 1)) (c : C i) :
    S.Δ i (v, c) = (S.δs (i + 1) v, S.φs (i + 1) v - d i c) := rfl

variable (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)

include hdd in
theorem Stage.Δ_Δ (i : ℕ) (x : S.G i) : S.Δ (i + 1) (S.Δ i x) = 0 := by
  obtain ⟨v, c⟩ := x
  rw [Stage.Δ_apply, Stage.Δ_apply, Prod.mk_eq_zero]
  refine ⟨S.δs_δs (by omega) v, ?_⟩
  rw [map_sub, ← S.d_φs (by omega) v, sub_sub_cancel]
  have h := LinearMap.congr_fun (hdd i) c
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

theorem Stage.Δ_exact (i : ℕ) (x : S.G (i + 1)) (hx : S.Δ (i + 1) x = 0) : x ∈ LinearMap.range (S.Δ i) := by
  obtain ⟨v, c⟩ := x
  rw [Stage.Δ_apply, Prod.mk_eq_zero, sub_eq_zero] at hx
  obtain ⟨hδ, hφ⟩ := hx
  obtain ⟨w, hw⟩ := S.s_inj (by omega) v hδ ⟨c, hφ.symm⟩
  have hcyc : d (i + 1) (c - S.φs (i + 1) w) = 0 := by
    rw [map_sub, ← hφ, S.d_φs (by omega) w, hw, sub_self]
  obtain ⟨u, hu, c'', hc''⟩ := S.s_surj i _ hcyc
  refine ⟨(w + u, c''), ?_⟩
  rw [Stage.Δ_apply, map_add, hw, hu, add_zero, map_add]
  congr 1
  rw [hc'']
  abel

theorem flat_prod (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P P' _ _ _ _ f hf
  have hM := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have hN := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have key : ∀ z, TensorProduct.prodRight R R P' M N (f.rTensor (M × N) z) =
      LinearMap.prodMap (f.rTensor M) (f.rTensor N) (TensorProduct.prodRight R R P M N z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p mn => simp [LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro z w h
  apply (TensorProduct.prodRight R R P M N).injective
  have h' := congrArg (TensorProduct.prodRight R R P' M N) h
  rw [key, key, LinearMap.prodMap_apply, LinearMap.prodMap_apply, Prod.mk.injEq] at h'
  exact Prod.ext (hM h'.1) (hN h'.2)

variable [IsNoetherianRing R] [∀ i, Module.Flat R (C i)]

include hdd in

theorem Stage.flat_ker_Δ (hbdd : ∀ i, n < i → Subsingleton (C i)) (i : ℕ) :
    Module.Flat R (LinearMap.ker (S.Δ i)) := by

  suffices h : ∀ t i, n ≤ i + t → Module.Flat R (LinearMap.ker (S.Δ i)) from h n i (by omega)
  intro t
  induction t with
  | zero =>
    intro i hi

    haveI : Subsingleton (S.K (i + 2)) := by
      rw [show S.K (i + 2) = (Fin (S.m (i + 2)) → R) from rfl, S.bdd (i + 2) (by omega)]
      infer_instance
    haveI : Subsingleton (C (i + 1)) := hbdd (i + 1) (by omega)
    have htop : LinearMap.ker (S.Δ i) = ⊤ := by
      ext x; simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]; exact Subsingleton.elim _ _
    rw [htop]
    haveI : Module.Flat R (S.G i) := flat_prod _ _
    exact Module.Flat.of_linearEquiv (Submodule.topEquiv (R := R) (M := S.G i))
  | succ t ih =>
    intro i hi
    by_cases hni : n ≤ i + t
    · exact ih i hni
    · haveI := ih (i + 1) (by omega)
      haveI : Module.Flat R (S.G i) := flat_prod _ _

      let g : S.G i →ₗ[R] LinearMap.ker (S.Δ (i + 1)) :=
        LinearMap.codRestrict _ (S.Δ i) (fun x => LinearMap.mem_ker.mpr (S.Δ_Δ hdd i x))
      have hg : Function.Surjective g := by
        intro z
        obtain ⟨x, hx⟩ := S.Δ_exact i z.1 (LinearMap.mem_ker.mp z.2)
        exact ⟨x, Subtype.ext hx⟩
      have hker : LinearMap.ker g = LinearMap.ker (S.Δ i) := LinearMap.ker_codRestrict _ _ _
      rw [← hker]
      exact Module.Flat.ker_of_surjective_of_flat g hg

end Small

end MumfordModel

namespace MumfordModel

variable {R : Type u} [CommRing R]
variable {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  {d : ∀ i, C i →ₗ[R] C (i + 1)} {n : ℕ}

section Final

variable (S : Stage C d n 1)

abbrev Stage.Z0 : Submodule R (S.G 0) := LinearMap.ker (S.Δ 0)

theorem Stage.mem_Z0 (v : S.K 1) (c : C 0) : (v, c) ∈ S.Z0 ↔ S.δs 1 v = 0 ∧ S.φs 1 v = d 0 c := by
  rw [LinearMap.mem_ker, Stage.Δ_apply, Prod.mk_eq_zero, sub_eq_zero]

theorem Stage.finite_Z0 [IsNoetherianRing R] (hfin0 : Module.Finite R (LinearMap.ker (d 0))) :
    Module.Finite R S.Z0 := by
  let pr : S.Z0 →ₗ[R] S.K 1 := LinearMap.fst R _ _ ∘ₗ S.Z0.subtype
  haveI : Module.Finite R (LinearMap.range pr) := inferInstance
  haveI : Module.Finite R (S.Z0 ⧸ LinearMap.ker pr) := Module.Finite.equiv pr.quotKerEquivRange.symm
  have h1 : ∀ c : LinearMap.ker (d 0), ((LinearMap.inr R (S.K 1) (C 0)) ∘ₗ (LinearMap.ker (d 0)).subtype) c ∈ S.Z0 := by
    intro c
    rw [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.inr_apply, Stage.mem_Z0, map_zero, map_zero,
      LinearMap.mem_ker.mp c.2]
    exact ⟨rfl, rfl⟩
  let e₁ : LinearMap.ker (d 0) →ₗ[R] S.Z0 :=
    LinearMap.codRestrict S.Z0 ((LinearMap.inr R (S.K 1) (C 0)) ∘ₗ (LinearMap.ker (d 0)).subtype) h1
  have h2 : ∀ c : LinearMap.ker (d 0), e₁ c ∈ LinearMap.ker pr := fun c => LinearMap.mem_ker.mpr rfl
  let e : LinearMap.ker (d 0) →ₗ[R] LinearMap.ker pr := LinearMap.codRestrict _ e₁ h2
  have he : Function.Surjective e := by
    rintro ⟨⟨⟨v, c⟩, hz⟩, hv⟩
    have hv0 : v = 0 := LinearMap.mem_ker.mp hv
    subst hv0
    have hc : d 0 c = 0 := by rw [Stage.mem_Z0, map_zero, map_zero] at hz; exact hz.2.symm
    exact ⟨⟨c, LinearMap.mem_ker.mpr hc⟩, rfl⟩
  haveI : Module.Finite R (LinearMap.ker pr) := Module.Finite.of_surjective e he
  exact Module.Finite.of_submodule_quotient (LinearMap.ker pr)

theorem Stage.projective_Z0 [IsNoetherianRing R] [∀ i, Module.Flat R (C i)]
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0))) : Module.Projective R S.Z0 := by
  haveI := S.finite_Z0 hfin0
  haveI : Module.Flat R S.Z0 := S.flat_ker_Δ hdd hbdd 0
  haveI : Module.FinitePresentation R S.Z0 := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

abbrev Stage.U (i : ℕ) : Type u := S.K i × S.G i

def Stage.Sfin : (i : ℕ) → Submodule R (S.U i)
  | 0 => LinearMap.range (LinearMap.inr R (S.K 0) (S.G 0) ∘ₗ S.Z0.subtype)
  | (j + 1) => LinearMap.range (LinearMap.inl R (S.K (j + 1)) (S.G (j + 1)))

theorem Stage.Sfin_zero : S.Sfin 0 = LinearMap.range (LinearMap.inr R (S.K 0) (S.G 0) ∘ₗ S.Z0.subtype) := rfl

theorem Stage.Sfin_succ (j : ℕ) : S.Sfin (j + 1) = LinearMap.range (LinearMap.inl R (S.K (j + 1)) (S.G (j + 1))) := rfl

theorem Stage.mem_Sfin_zero {x : S.U 0} : x ∈ S.Sfin 0 ↔ x.1 = 0 ∧ x.2 ∈ S.Z0 := by
  rw [Stage.Sfin_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨rfl, z.2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨x.2, h2⟩, Prod.ext h1.symm rfl⟩

theorem Stage.mem_Sfin_succ {j : ℕ} {x : S.U (j + 1)} : x ∈ S.Sfin (j + 1) ↔ x.2 = 0 := by
  rw [Stage.Sfin_succ, LinearMap.mem_range]
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨x.1, Prod.ext rfl h.symm⟩

abbrev Stage.KK (i : ℕ) : Type u := ↥(S.Sfin i)

def Stage.AΔ (i : ℕ) : S.U i →ₗ[R] S.U (i + 1) :=
  LinearMap.inl R (S.K (i + 1)) (S.G (i + 1)) ∘ₗ
    (S.δs i ∘ₗ LinearMap.fst R _ _ + LinearMap.fst R _ _ ∘ₗ LinearMap.snd R _ _)

theorem Stage.AΔ_apply (i : ℕ) (x : S.U i) : S.AΔ i x = (S.δs i x.1 + x.2.1, 0) := rfl

theorem Stage.AΔ_mem (i : ℕ) (x : S.U i) : S.AΔ i x ∈ S.Sfin (i + 1) := by
  rw [Stage.mem_Sfin_succ, Stage.AΔ_apply]

def Stage.δK (i : ℕ) : S.KK i →ₗ[R] S.KK (i + 1) :=
  LinearMap.codRestrict _ (S.AΔ i ∘ₗ (S.Sfin i).subtype) (fun x => S.AΔ_mem i x)

theorem Stage.δK_val (i : ℕ) (x : S.KK i) : ((S.δK i x : S.KK (i + 1)) : S.U (i + 1)) = (S.δs i x.1.1 + x.1.2.1, 0) := rfl

def Stage.Aφ (i : ℕ) : S.U i →ₗ[R] C i :=
  S.φs i ∘ₗ LinearMap.fst R _ _ + LinearMap.snd R _ _ ∘ₗ LinearMap.snd R _ _

def Stage.φK (i : ℕ) : S.KK i →ₗ[R] C i := S.Aφ i ∘ₗ (S.Sfin i).subtype

theorem Stage.φK_apply (i : ℕ) (x : S.KK i) : S.φK i x = S.φs i x.1.1 + x.1.2.2 := rfl

theorem Stage.finite_KK [IsNoetherianRing R] (hfin0 : Module.Finite R (LinearMap.ker (d 0))) (i : ℕ) :
    Module.Finite R (S.KK i) := by
  cases i with
  | zero =>
    haveI := S.finite_Z0 hfin0
    exact (inferInstance : Module.Finite R (LinearMap.range (LinearMap.inr R (S.K 0) (S.G 0) ∘ₗ S.Z0.subtype)))
  | succ j =>
    exact (inferInstance : Module.Finite R (LinearMap.range (LinearMap.inl R (S.K (j + 1)) (S.G (j + 1)))))

theorem Stage.projective_KK [IsNoetherianRing R] [∀ i, Module.Flat R (C i)]
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0))) (i : ℕ) : Module.Projective R (S.KK i) := by
  cases i with
  | zero =>
    haveI := S.projective_Z0 hdd hbdd hfin0
    have hinj : Function.Injective (LinearMap.inr R (S.K 0) (S.G 0) ∘ₗ S.Z0.subtype) :=
      LinearMap.inr_injective.comp (Submodule.subtype_injective _)
    exact Module.Projective.of_equiv (LinearEquiv.ofInjective _ hinj)
  | succ j =>
    exact Module.Projective.of_equiv
      (LinearEquiv.ofInjective (LinearMap.inl R (S.K (j + 1)) (S.G (j + 1))) LinearMap.inl_injective)

theorem Stage.subsingleton_KK {i : ℕ} (hi : n < i) : Subsingleton (S.KK i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  haveI : Subsingleton (S.K (j + 1)) := by
    rw [show S.K (j + 1) = (Fin (S.m (j + 1)) → R) from rfl, S.bdd (j + 1) hi]
    infer_instance
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := S.mem_Sfin_succ.mp x.2
  have hy := S.mem_Sfin_succ.mp y.2
  exact Prod.ext (Subsingleton.elim _ _) (hx.trans hy.symm)

theorem Stage.δK_δK_zero (x : S.KK 0) : S.δK 1 (S.δK 0 x) = 0 := by
  obtain ⟨h1, h2⟩ := S.mem_Sfin_zero.mp x.2
  apply Subtype.ext
  rw [Stage.δK_val, Submodule.coe_zero, Prod.mk_eq_zero]
  refine ⟨?_, rfl⟩
  rw [Stage.δK_val]
  show S.δs 1 (S.δs 0 x.1.1 + x.1.2.1) + 0 = 0
  rw [add_zero, map_add, h1, map_zero, map_zero]
  simp only [zero_add]
  exact ((S.mem_Z0 _ _).mp h2).1

theorem Stage.δK_δK_succ (j : ℕ) (x : S.KK (j + 1)) : S.δK (j + 1 + 1) (S.δK (j + 1) x) = 0 := by
  have h2 := S.mem_Sfin_succ.mp x.2
  apply Subtype.ext
  rw [Stage.δK_val, Submodule.coe_zero, Prod.mk_eq_zero]
  refine ⟨?_, rfl⟩
  rw [Stage.δK_val]
  show S.δs (j + 1 + 1) (S.δs (j + 1) x.1.1 + x.1.2.1) + 0 = 0
  rw [add_zero, map_add, S.δs_δs (by omega), zero_add, show x.1.2.1 = (x.1.2).1 from rfl, h2,
    Prod.fst_zero, map_zero]

theorem Stage.δK_δK (i : ℕ) : S.δK (i + 1) ∘ₗ S.δK i = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  cases i with
  | zero => exact S.δK_δK_zero x
  | succ j => exact S.δK_δK_succ j x

theorem Stage.d_φK_zero (x : S.KK 0) : d 0 (S.φK 0 x) = S.φK 1 (S.δK 0 x) := by
  obtain ⟨h1, h2⟩ := S.mem_Sfin_zero.mp x.2
  rw [Stage.φK_apply, Stage.φK_apply]
  show d 0 (S.φs 0 x.1.1 + x.1.2.2) = S.φs 1 (S.δs 0 x.1.1 + x.1.2.1) + 0
  rw [add_zero, h1, map_zero, map_zero]
  simp only [zero_add]
  exact ((S.mem_Z0 _ _).mp h2).2.symm

theorem Stage.d_φK_succ (j : ℕ) (x : S.KK (j + 1)) :
    d (j + 1) (S.φK (j + 1) x) = S.φK (j + 1 + 1) (S.δK (j + 1) x) := by
  have h2 := S.mem_Sfin_succ.mp x.2
  rw [Stage.φK_apply, Stage.φK_apply]
  show d (j + 1) (S.φs (j + 1) x.1.1 + x.1.2.2) = S.φs (j + 1 + 1) (S.δs (j + 1) x.1.1 + x.1.2.1) + 0
  rw [add_zero, show x.1.2.1 = (x.1.2).1 from rfl, show x.1.2.2 = (x.1.2).2 from rfl, h2,
    Prod.fst_zero, Prod.snd_zero, add_zero, add_zero, S.d_φs (by omega)]

theorem Stage.d_φK (i : ℕ) : d i ∘ₗ S.φK i = S.φK (i + 1) ∘ₗ S.δK i := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  cases i with
  | zero => exact S.d_φK_zero x
  | succ j => exact S.d_φK_succ j x

theorem Stage.h0inj (x : S.KK 0) (hδ : S.δK 0 x = 0) (hφ : S.φK 0 x = 0) : x = 0 := by
  obtain ⟨h1, h2⟩ := S.mem_Sfin_zero.mp x.2
  have hb : x.1.2.1 = 0 := by
    have := congrArg (fun z : S.KK 1 => (z : S.U 1).1) hδ
    simp only [Stage.δK_val, Submodule.coe_zero, Prod.fst_zero] at this
    rwa [h1, map_zero, zero_add] at this
  have hc : x.1.2.2 = 0 := by
    rw [Stage.φK_apply, h1, map_zero, zero_add] at hφ; exact hφ
  apply Subtype.ext
  rw [Submodule.coe_zero]
  exact Prod.ext h1 (Prod.ext hb hc)

theorem Stage.h0surj (y : C 0) (hy : d 0 y = 0) : ∃ x : S.KK 0, S.δK 0 x = 0 ∧ S.φK 0 x = y := by
  have hz : ((0 : S.K 1), y) ∈ S.Z0 := by
    rw [Stage.mem_Z0, map_zero, map_zero, hy]; exact ⟨rfl, rfl⟩
  refine ⟨⟨((0 : S.K 0), ((0 : S.K 1), y)), S.mem_Sfin_zero.mpr ⟨rfl, hz⟩⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Stage.δK_val, Submodule.coe_zero, Prod.mk_eq_zero]
    exact ⟨by show S.δs 0 0 + 0 = 0; rw [map_zero, add_zero], rfl⟩
  · rw [Stage.φK_apply]; show S.φs 0 0 + y = y; rw [map_zero, zero_add]

theorem Stage.hKinj_aux (i : ℕ) (x : S.KK (i + 1)) (hδ : S.δK (i + 1) x = 0) :
    x.1.2 = 0 ∧ S.δs (i + 1) x.1.1 = 0 ∧ S.φK (i + 1) x = S.φs (i + 1) x.1.1 := by
  have h2 := S.mem_Sfin_succ.mp x.2
  have hb : x.1.2.1 = 0 := by rw [show x.1.2.1 = (x.1.2).1 from rfl, h2, Prod.fst_zero]
  have hc : x.1.2.2 = 0 := by rw [show x.1.2.2 = (x.1.2).2 from rfl, h2, Prod.snd_zero]
  refine ⟨h2, ?_, ?_⟩
  · have := congrArg (fun z : S.KK (i + 1 + 1) => (z : S.U (i + 1 + 1)).1) hδ
    simp only [Stage.δK_val, Submodule.coe_zero, Prod.fst_zero] at this
    rwa [hb, add_zero] at this
  · rw [Stage.φK_apply, hc, add_zero]

theorem Stage.hKinj_zero (x : S.KK 1) (hδ : S.δK 1 x = 0)
    (hφ : S.φK 1 x ∈ LinearMap.range (d 0)) : x ∈ LinearMap.range (S.δK 0) := by
  obtain ⟨h2, ha, hφeq⟩ := S.hKinj_aux 0 x hδ
  rw [hφeq] at hφ
  obtain ⟨c', hc'⟩ := hφ
  have hz : (x.1.1, c') ∈ S.Z0 := by rw [Stage.mem_Z0]; exact ⟨ha, hc'.symm⟩
  refine ⟨⟨((0 : S.K 0), (x.1.1, c')), S.mem_Sfin_zero.mpr ⟨rfl, hz⟩⟩, Subtype.ext ?_⟩
  rw [Stage.δK_val]
  show (S.δs 0 0 + x.1.1, (0 : S.G 1)) = x.1
  simp only [map_zero, zero_add]
  exact Prod.ext rfl h2.symm

theorem Stage.hKinj_succ (j : ℕ) (x : S.KK (j + 1 + 1)) (hδ : S.δK (j + 1 + 1) x = 0)
    (hφ : S.φK (j + 1 + 1) x ∈ LinearMap.range (d (j + 1))) : x ∈ LinearMap.range (S.δK (j + 1)) := by
  obtain ⟨h2, ha, hφeq⟩ := S.hKinj_aux (j + 1) x hδ
  rw [hφeq] at hφ
  obtain ⟨w, hw⟩ := S.s_inj (by omega) x.1.1 ha hφ
  refine ⟨⟨(w, 0), S.mem_Sfin_succ.mpr rfl⟩, Subtype.ext ?_⟩
  rw [Stage.δK_val]
  show (S.δs (j + 1) w + 0, (0 : S.G (j + 1 + 1))) = x.1
  rw [add_zero, hw]
  exact Prod.ext rfl h2.symm

theorem Stage.hKinj (i : ℕ) (x : S.KK (i + 1)) (hδ : S.δK (i + 1) x = 0)
    (hφ : S.φK (i + 1) x ∈ LinearMap.range (d i)) : x ∈ LinearMap.range (S.δK i) := by
  cases i with
  | zero => exact S.hKinj_zero x hδ hφ
  | succ j => exact S.hKinj_succ j x hδ hφ

theorem Stage.hKsurj (i : ℕ) (y : C (i + 1)) (hy : d (i + 1) y = 0) :
    ∃ x : S.KK (i + 1), S.δK (i + 1) x = 0 ∧ S.φK (i + 1) x - y ∈ LinearMap.range (d i) := by
  obtain ⟨v, hv, hvy⟩ := S.s_surj i y hy
  refine ⟨⟨(v, 0), S.mem_Sfin_succ.mpr rfl⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Stage.δK_val, Submodule.coe_zero, Prod.mk_eq_zero]
    exact ⟨by show S.δs (i + 1) v + 0 = 0; rw [add_zero, hv], rfl⟩
  · rw [Stage.φK_apply]
    show S.φs (i + 1) v + 0 - y ∈ LinearMap.range (d i)
    rw [add_zero]; exact hvy

end Final

end MumfordModel

open MumfordModel in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (K : ℕ → Type u) (_ : ∀ i, AddCommGroup (K i)) (_ : ∀ i, Module R (K i))
      (_ : ∀ i, Module.Finite R (K i)) (_ : ∀ i, Module.Projective R (K i))
      (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, n < i → Subsingleton (K i))
      (φ : ∀ i, K i →ₗ[R] C i) (_ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i),
      (∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0) ∧
      (∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y) ∧
      (∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
        x ∈ LinearMap.range (δ i)) ∧
      (∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
        ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) := by
  obtain ⟨S⟩ := Stage.nonempty_descend (C := C) (d := d) (n := n) hbdd hfin
  exact ⟨S.KK, fun _ => inferInstance, fun _ => inferInstance, S.finite_KK hfin0, S.projective_KK hdd hbdd hfin0,
    S.δK, S.δK_δK, fun i hi => S.subsingleton_KK hi, S.φK, S.d_φK,
    S.h0inj, S.h0surj, S.hKinj, S.hKsurj⟩

end S_Module_exists_projective_complex_quasiIso_of_flat_complex
end P2MW
export P2MW.S_Module_exists_projective_complex_quasiIso_of_flat_complex (solution)
