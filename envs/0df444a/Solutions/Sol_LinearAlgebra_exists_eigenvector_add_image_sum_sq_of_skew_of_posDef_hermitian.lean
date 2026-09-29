-- Prove2me | solution 1 for LinearAlgebra.exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6aed0359-bdd6-52de-8a6e-9c0afab57031

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian

set_option autoImplicit false

noncomputable section

namespace WsB
namespace EIG

section Piece

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem form_zero_left (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    {n : W} (hn : n ∈ M₀) : B 0 n = 0 := by
  have h := hlin (-1) 0 M₀.zero_mem 0 M₀.zero_mem n hn
  rw [smul_zero, add_zero] at h
  linear_combination h

def orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) : Submodule ℂ W where
  carrier := {w | w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0}
  add_mem' {a b} ha hb := ⟨M₀.add_mem ha.1 hb.1, fun n hn => by
    have h := hlin 1 a ha.1 b hb.1 n (hNM hn)
    rw [one_smul, one_mul, ha.2 n hn, hb.2 n hn, add_zero] at h
    exact h⟩
  zero_mem' := ⟨M₀.zero_mem, fun n hn => form_zero_left M₀ B hlin (hNM hn)⟩
  smul_mem' z a ha := ⟨M₀.smul_mem z ha.1, fun n hn => by
    have h := hlin z a ha.1 0 M₀.zero_mem n (hNM hn)
    rw [add_zero, ha.2 n hn, mul_zero, zero_add, form_zero_left M₀ B hlin (hNM hn)] at h
    exact h⟩

theorem mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (w : W) : w ∈ orthoIn M₀ N B hlin hNM ↔ w ∈ M₀ ∧ ∀ n ∈ N, B w n = 0 := Iff.rfl

theorem orthoIn_mapsTo (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (admD : W → W) (hDM : ∀ w ∈ M₀, admD w ∈ M₀) (hDN : ∀ n ∈ N, admD n ∈ N)
    (hskew : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (admD w) w' = - B w (admD w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, admD w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hDM w hw.1, fun n hn => ?_⟩
  rw [hskew w hw.1 n (hNM hn), hw.2 (admD n) (hDN n hn), neg_zero]

theorem orthoIn_mapsTo_of_isometry (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, ∃ n' ∈ N, T n' = n)
    (hTB : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) (T w') = B w w') :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  refine ⟨hTM w hw.1, fun n hn => ?_⟩
  obtain ⟨n', hn', rfl⟩ := hTN n hn
  rw [hTB w hw.1 n' (hNM hn')]
  exact hw.2 n' hn'

theorem eq_zero_of_mem_orthoIn {Z : Type*} [AddCommGroup Z] (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) (Λ : W → Z)
    (hker : ∀ w ∈ M₀, Λ w = 0 → w ∈ N) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, Λ w = 0 → w = 0 := by
  intro w hw hΛ
  by_contra hne
  have h := hpos w hw.1 hne
  rw [hw.2 w (hker w hw.1 hΛ), Complex.zero_re] at h
  exact lt_irrefl _ h

theorem exists_ne_zero_mem_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] (hlt : N < M₀) :
    ∃ w ∈ orthoIn M₀ N B hlin hNM, w ≠ 0 := by
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNM

  let b := Module.finBasis ℂ N
  let φ : M₀ →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    { toFun := fun w i => B w (b i)
      map_add' := fun x y => by
        funext i
        have h := hlin 1 x x.2 y y.2 (b i) (hNM (b i).2)
        rw [one_smul, one_mul] at h
        simpa using h
      map_smul' := fun z x => by
        funext i
        have h := hlin z x x.2 0 M₀.zero_mem (b i) (hNM (b i).2)
        rw [add_zero, form_zero_left M₀ B hlin (hNM (b i).2), add_zero] at h
        simpa using h }

  have hker : ∀ x : M₀, φ x = 0 → (x : W) ∈ orthoIn M₀ N B hlin hNM := by
    intro x hx
    refine ⟨x.2, fun n hn => ?_⟩

    have hrepr : (⟨n, hn⟩ : N) = ∑ i, b.repr ⟨n, hn⟩ i • b i := (b.sum_repr ⟨n, hn⟩).symm
    have hn' : n = ∑ i, b.repr ⟨n, hn⟩ i • (b i : W) := by
      have := congrArg Subtype.val hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this

    have hsum : ∀ (s : Finset (Fin (Module.finrank ℂ N))),
        B (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) x = ∑ i ∈ s, b.repr ⟨n, hn⟩ i * B (b i) x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact form_zero_left M₀ B hlin x.2
      | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        have hmem : (∑ i ∈ s, b.repr ⟨n, hn⟩ i • (b i : W)) ∈ M₀ :=
          M₀.sum_mem fun i _ => M₀.smul_mem _ (hNM (b i).2)
        exact hlin _ _ (hNM (b j).2) _ hmem x x.2
    have hBn : B n x = ∑ i, b.repr ⟨n, hn⟩ i * B (b i) x := by
      conv_lhs => rw [hn']
      exact hsum Finset.univ
    rw [hsymm n (hNM hn) x x.2, hBn]
    have hzero : (∑ i, b.repr ⟨n, hn⟩ i * B (b i) x) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : B (b i) x = 0 := by
        rw [hsymm x x.2 (b i) (hNM (b i).2)]
        have := congrFun hx i
        simp only [Pi.zero_apply] at this
        change B x (b i) = 0 at this
        rw [this, map_zero]
      rw [hi, mul_zero]
    rw [hzero, map_zero]

  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ N := by
    calc Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ N) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ N := by simp
  have hlt' : Module.finrank ℂ N < Module.finrank ℂ M₀ := Submodule.finrank_lt_finrank_of_lt hlt
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker φ) := by omega
  have hnebot : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnebot
  exact ⟨(x : W), hker x (LinearMap.mem_ker.1 hx), fun h => hx0 (Subtype.ext h)⟩

theorem eq_zero_of_mem_inf_orthoIn (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) {w : W} (hwN : w ∈ N) (hwP : w ∈ orthoIn M₀ N B hlin hNM) : w = 0 := by
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hwP
  by_contra hne
  have h := hpos w hwM hne
  rw [hperp w hwN, Complex.zero_re] at h
  exact lt_irrefl _ h

theorem sup_orthoIn_eq (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hNM : N ≤ M₀) [FiniteDimensional ℂ M₀] :
    N ⊔ orthoIn M₀ N B hlin hNM = M₀ := by
  have hPM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  refine le_antisymm (sup_le hNM hPM) ?_
  by_contra hcon
  have hlt : N ⊔ orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne (sup_le hNM hPM) fun h => hcon h.ge
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_mem_orthoIn M₀ (N ⊔ orthoIn M₀ N B hlin hNM) B hlin hsymm
    (sup_le hNM hPM) hlt
  obtain ⟨hwM, hwperp⟩ := (mem_orthoIn M₀ _ B hlin (sup_le hNM hPM) w).1 hw
  have hwP : w ∈ orthoIn M₀ N B hlin hNM :=
    (mem_orthoIn M₀ N B hlin hNM w).2 ⟨hwM, fun n hn => hwperp n (Submodule.mem_sup_left hn)⟩
  have hself : B w w = 0 := hwperp w (Submodule.mem_sup_right hwP)
  have := hpos w hwM hw0
  rw [hself, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem orthoIn_mapsTo_comp (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T₁ T₂ : W → W)
    (h₁ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ w ∈ orthoIn M₀ N B hlin hNM)
    (h₂ : ∀ w ∈ orthoIn M₀ N B hlin hNM, T₂ w ∈ orthoIn M₀ N B hlin hNM) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T₁ (T₂ w) ∈ orthoIn M₀ N B hlin hNM :=
  fun w hw => h₁ _ (h₂ w hw)

theorem exists_mem_orthoIn_map_eq_of_killed {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (M₀ : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    [FiniteDimensional ℂ M₀] (Φ : W →ₗ[ℂ] Z) (δ : W → W) (δ' : Z → Z)
    (hδM : ∀ x ∈ M₀, δ x ∈ M₀)
    (hδP : ∀ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right,
      δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right)
    (hcomm : ∀ x ∈ M₀, Φ (δ x) = δ' (Φ x))
    {v₀ : Z} (hv : ∃ y ∈ M₀, Φ y = v₀) (hkill : δ' v₀ = 0) :
    ∃ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right, Φ x = v₀ ∧ δ x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have hdec := sup_orthoIn_eq M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hsymm hpos inf_le_right
  rw [← hdec] at hy
  obtain ⟨n, hn, x, hx, rfl⟩ := Submodule.mem_sup.1 hy
  have hnK : Φ n = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hn).1
  have hxM : x ∈ M₀ := ((mem_orthoIn M₀ _ B hlin inf_le_right x).1 hx).1
  have hΦx : Φ x = Φ (n + x) := by rw [map_add, hnK, zero_add]
  refine ⟨x, hx, hΦx, ?_⟩
  have hδx : δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right := hδP x hx
  have hδK : δ x ∈ LinearMap.ker Φ ⊓ M₀ := by
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hδM x hxM⟩
    rw [hcomm x hxM, hΦx, hkill]
  exact eq_zero_of_mem_inf_orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hpos inf_le_right hδK hδx

theorem exists_mem_orthoIn_map_eq_of_killed' {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (M₀ admE : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (hEM : admE ≤ M₀) [FiniteDimensional ℂ admE] (Φ : W →ₗ[ℂ] Z) (δ : W → W) (δ' : Z → Z)
    (hδM : ∀ x ∈ M₀, δ x ∈ M₀)
    (hδP : ∀ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right,
      δ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right)
    (hcomm : ∀ x ∈ M₀, Φ (δ x) = δ' (Φ x))
    (hproj : ∀ z ∈ LinearMap.ker Φ ⊓ M₀, ∃ e ∈ LinearMap.ker Φ ⊓ admE, ∀ x ∈ admE, B x z = B x e)
    {v₀ : Z} (hv : ∃ y ∈ admE, Φ y = v₀) (hkill : δ' v₀ = 0) :
    ∃ x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right, Φ x = v₀ ∧ δ x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have hlinE : ∀ (z : ℂ), ∀ w₁ ∈ admE, ∀ w₂ ∈ admE, ∀ w' ∈ admE, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w' :=
    fun z w₁ h₁ w₂ h₂ w' h' => hlin z w₁ (hEM h₁) w₂ (hEM h₂) w' (hEM h')
  have hsymmE : ∀ w ∈ admE, ∀ w' ∈ admE, B w' w = (starRingEnd ℂ) (B w w') :=
    fun w hw w' hw' => hsymm w (hEM hw) w' (hEM hw')
  have hposE : ∀ w ∈ admE, w ≠ 0 → 0 < (B w w).re := fun w hw => hpos w (hEM hw)
  have hdec := sup_orthoIn_eq admE (LinearMap.ker Φ ⊓ admE) B hlinE hsymmE hposE inf_le_right
  rw [← hdec] at hy
  obtain ⟨n, hn, x, hx, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨hxE, hxperp⟩ := (mem_orthoIn admE _ B hlinE inf_le_right x).1 hx
  have hnK : Φ n = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hn).1
  have hΦx : Φ x = Φ (n + x) := by rw [map_add, hnK, zero_add]

  have hxW : x ∈ orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin inf_le_right := by
    refine (mem_orthoIn M₀ _ B hlin inf_le_right x).2 ⟨hEM hxE, fun z hz => ?_⟩
    obtain ⟨e, he, hpair⟩ := hproj z hz
    rw [hpair x hxE]
    exact hxperp e he
  refine ⟨x, hxW, hΦx, ?_⟩
  have hδx := hδP x hxW
  have hδK : δ x ∈ LinearMap.ker Φ ⊓ M₀ := by
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hδM x (hEM hxE)⟩
    rw [hcomm x (hEM hxE), hΦx, hkill]
  exact eq_zero_of_mem_inf_orthoIn M₀ (LinearMap.ker Φ ⊓ M₀) B hlin hpos inf_le_right hδK hδx

theorem orthoIn_mapsTo_of_symm (M₀ N : Submodule ℂ W) (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hNM : N ≤ M₀) (T : W → W) (hTM : ∀ w ∈ M₀, T w ∈ M₀) (hTN : ∀ n ∈ N, T n ∈ N)
    (hsym : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (T w) w' = B w (T w')) :
    ∀ w ∈ orthoIn M₀ N B hlin hNM, T w ∈ orthoIn M₀ N B hlin hNM := by
  intro w hw
  obtain ⟨hwM, hperp⟩ := (mem_orthoIn M₀ N B hlin hNM w).1 hw
  refine (mem_orthoIn M₀ N B hlin hNM (T w)).2 ⟨hTM w hwM, fun n hn => ?_⟩
  rw [hsym w hwM n (hNM hn)]
  exact hperp (T n) (hTN n hn)

theorem exists_eigen_decomposition :
    ∀ (n : ℕ) (M₀ : Submodule ℂ W) [FiniteDimensional ℂ M₀], Module.finrank ℂ M₀ = n →
      ∀ (B : W → W → ℂ),
        (∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') →
        (∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w')) →
        (∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re) →
        ∀ (Ω : W →ₗ[ℂ] W), (∀ w ∈ M₀, Ω w ∈ M₀) → (∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w')) →
          ∀ z ∈ M₀, ∃ (s : Finset ℂ) (f : ℂ → W),
            (∀ μ ∈ s, f μ ∈ M₀ ∧ Ω (f μ) = μ • f μ) ∧ z = ∑ μ ∈ s, f μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M₀ _ hn B hlin hsymm hpos Ω hΩM hΩsymm z hz
  by_cases hn0 : n = 0
  ·
    have hbot : M₀ = ⊥ := Submodule.finrank_eq_zero.1 (hn.trans hn0)
    rw [hbot] at hz
    refine ⟨∅, fun _ => 0, fun μ hμ => absurd hμ (by simp), ?_⟩
    rw [Finset.sum_empty]; exact (Submodule.mem_bot ℂ).1 hz

  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : Nontrivial M₀ := by
    rw [← Module.finrank_pos_iff (R := ℂ)]; omega
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Ω.restrict hΩM)
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  have hyW : Ω (y : W) = c • (y : W) := by
    have h := hy.apply_eq_smul
    have h' := congrArg Subtype.val h
    rw [LinearMap.restrict_apply] at h'
    simpa using h'
  have hy0 : (y : W) ≠ 0 := fun h => hy.2 (Subtype.ext h)

  set N : Submodule ℂ W := Submodule.span ℂ {(y : W)} with hNdef
  have hNM : N ≤ M₀ := by
    rw [hNdef, Submodule.span_le]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]; exact y.2
  have hNΩ : ∀ m ∈ N, Ω m ∈ N := by
    intro m hm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [map_smul, hyW]
    exact N.smul_mem a (N.smul_mem c (Submodule.mem_span_singleton_self (y : W)))
  have hFM : orthoIn M₀ N B hlin hNM ≤ M₀ := fun w hw => ((mem_orthoIn M₀ N B hlin hNM w).1 hw).1
  haveI : FiniteDimensional ℂ (orthoIn M₀ N B hlin hNM) := Submodule.finiteDimensional_of_le hFM
  have hyF : (y : W) ∉ orthoIn M₀ N B hlin hNM := by
    intro hyF
    have h := ((mem_orthoIn M₀ N B hlin hNM _).1 hyF).2 (y : W) (Submodule.mem_span_singleton_self _)
    have hp := hpos (y : W) y.2 hy0
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hFlt : orthoIn M₀ N B hlin hNM < M₀ := lt_of_le_of_ne hFM fun h => hyF (by rw [h]; exact y.2)
  have hFrank : Module.finrank ℂ (orthoIn M₀ N B hlin hNM) < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hFlt

  have hdec := sup_orthoIn_eq M₀ N B hlin hsymm hpos hNM
  rw [← hdec] at hz
  obtain ⟨m, hm, x, hx, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm

  have hFΩ : ∀ w ∈ orthoIn M₀ N B hlin hNM, Ω w ∈ orthoIn M₀ N B hlin hNM :=
    orthoIn_mapsTo_of_symm M₀ N B hlin hNM Ω hΩM hNΩ hΩsymm
  obtain ⟨s, f, hf, hxsum⟩ := ih (Module.finrank ℂ (orthoIn M₀ N B hlin hNM)) hFrank
    (orthoIn M₀ N B hlin hNM) rfl B
    (fun z w₁ h₁ w₂ h₂ w' h' => hlin z w₁ (hFM h₁) w₂ (hFM h₂) w' (hFM h'))
    (fun w hw w' hw' => hsymm w (hFM hw) w' (hFM hw'))
    (fun w hw => hpos w (hFM hw)) Ω hFΩ
    (fun w hw w' hw' => hΩsymm w (hFM hw) w' (hFM hw')) x hx

  classical
  refine ⟨insert c s, fun μ => (if μ ∈ s then f μ else 0) + (if μ = c then a • (y : W) else 0), ?_, ?_⟩
  · intro μ hμ
    constructor
    · refine M₀.add_mem ?_ ?_
      · split_ifs with h
        · exact hFM (hf μ h).1
        · exact M₀.zero_mem
      · split_ifs with h
        · exact M₀.smul_mem a y.2
        · exact M₀.zero_mem
    · rw [map_add, smul_add]
      congr 1
      · split_ifs with h
        · exact (hf μ h).2
        · simp
      · split_ifs with h
        · rw [map_smul, hyW, h, smul_comm]
        · simp
  · rw [Finset.sum_add_distrib]
    have h1 : ∑ μ ∈ insert c s, (if μ ∈ s then f μ else 0) = ∑ μ ∈ s, f μ := by
      by_cases hcs : c ∈ s
      · rw [Finset.insert_eq_of_mem hcs]
        exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
      · rw [Finset.sum_insert hcs, if_neg hcs, zero_add]
        exact Finset.sum_congr rfl fun μ hμ => if_pos hμ
    have h2 : ∑ μ ∈ insert c s, (if μ = c then a • (y : W) else 0) = a • (y : W) := by
      rw [Finset.sum_ite_eq' (insert c s) c]
      exact if_pos (Finset.mem_insert_self c s)
    rw [h1, h2, ← hxsum, add_comm]

end Piece

section KerIm

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem exists_eigen_add_image (M₀ : Submodule ℂ W) [FiniteDimensional ℂ M₀] (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (Ω : W →ₗ[ℂ] W) (hΩM : ∀ w ∈ M₀, Ω w ∈ M₀) (hΩsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w'))
    (c : ℂ) (z : W) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, Ω k = c • k ∧ ∃ x ∈ M₀, z = k + (Ω x - c • x) := by
  classical
  obtain ⟨s, f, hf, hzs⟩ := exists_eigen_decomposition (Module.finrank ℂ M₀) M₀ rfl B hlin hsymm hpos Ω hΩM hΩsymm z hz
  refine ⟨if c ∈ s then f c else 0, ?_, ?_, ∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ, ?_, ?_⟩
  · split_ifs with h
    · exact (hf c h).1
    · exact M₀.zero_mem
  · split_ifs with h
    · exact (hf c h).2
    · simp
  · exact M₀.sum_mem (fun μ hμ => M₀.smul_mem _ (hf μ (Finset.mem_of_mem_erase hμ)).1)
  · have hIm : Ω (∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ) - c • ∑ μ ∈ s.erase c, (μ - c)⁻¹ • f μ =
        ∑ μ ∈ s.erase c, f μ := by
      rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      have hne : μ - c ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ)
      rw [map_smul, (hf μ (Finset.mem_of_mem_erase hμ)).2, smul_smul, smul_smul, ← sub_smul]
      rw [show (μ - c)⁻¹ * μ - c * (μ - c)⁻¹ = 1 by field_simp, one_smul]
    rw [hIm, hzs]
    by_cases h : c ∈ s
    · rw [if_pos h, ← Finset.add_sum_erase s f h]
    · rw [if_neg h, zero_add, Finset.erase_eq_of_notMem h]

end KerIm

end WsB.EIG

theorem solution
    (V : Type*) [AddCommGroup V] [Module ℂ V] (M₀ : Submodule ℂ V) [Module.Finite ℂ M₀]
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (ι : Type*) [Fintype ι] (θ : ι → (V →ₗ[ℂ] V))
    (hθM : ∀ i : ι, ∀ w ∈ M₀, θ i w ∈ M₀)
    (hskew : ∀ i : ι, ∀ w ∈ M₀, ∀ w' ∈ M₀, B (θ i w) w' = -B w (θ i w'))
    (c : ℂ) (z : V) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, ∃ x ∈ M₀, (∑ i : ι, θ i * θ i) k = c • k ∧ z = k + ((∑ i : ι, θ i * θ i) x - c • x) := by
  classical
  set Ω : V →ₗ[ℂ] V := ∑ i : ι, θ i * θ i with hΩ
  have hΩM : ∀ w ∈ M₀, Ω w ∈ M₀ := by
    intro w hw
    rw [hΩ, LinearMap.sum_apply]
    exact M₀.sum_mem (fun i _ => hθM i _ (hθM i w hw))
  have hΩsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B (Ω w) w' = B w (Ω w') := by
    intro w hw w' hw'

    have hB0 : ∀ u ∈ M₀, B 0 u = 0 := fun u hu => WsB.EIG.form_zero_left M₀ B hlin hu
    have haddL : ∀ a ∈ M₀, ∀ b ∈ M₀, ∀ u ∈ M₀, B (a + b) u = B a u + B b u := by
      intro a ha b hb u hu; have h := hlin 1 a ha b hb u hu; rw [one_smul, one_mul] at h; exact h
    have haddR : ∀ u ∈ M₀, ∀ a ∈ M₀, ∀ b ∈ M₀, B u (a + b) = B u a + B u b := by
      intro u hu a ha b hb
      rw [hsymm (a + b) (M₀.add_mem ha hb) u hu, hsymm a ha u hu, hsymm b hb u hu, haddL a ha b hb u hu, map_add]
    have hsumL : ∀ (s : Finset ι) (f : ι → V), (∀ i, f i ∈ M₀) → ∀ u ∈ M₀, B (∑ i ∈ s, f i) u = ∑ i ∈ s, B (f i) u := by
      intro s f hf u hu
      induction s using Finset.induction_on with
      | empty => simp [hB0 u hu]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL _ (hf a) _ (M₀.sum_mem fun i _ => hf i) u hu, ih]
    have hsumR : ∀ (s : Finset ι) (f : ι → V), (∀ i, f i ∈ M₀) → ∀ u ∈ M₀, B u (∑ i ∈ s, f i) = ∑ i ∈ s, B u (f i) := by
      intro s f hf u hu
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        rw [hsymm 0 M₀.zero_mem u hu, hB0 u hu, map_zero]
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, haddR u hu _ (hf a) _ (M₀.sum_mem fun i _ => hf i), ih]
    rw [hΩ, LinearMap.sum_apply, LinearMap.sum_apply,
      hsumL _ (fun i => (θ i * θ i) w) (fun i => hθM i _ (hθM i w hw)) w' hw',
      hsumR _ (fun i => (θ i * θ i) w') (fun i => hθM i _ (hθM i w' hw')) w hw]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Module.End.mul_apply, Module.End.mul_apply, hskew i _ (hθM i w hw) w' hw', hskew i w hw _ (hθM i w' hw'), neg_neg]
  haveI : FiniteDimensional ℂ M₀ := inferInstance
  obtain ⟨k, hk, hkeig, x, hx, hzx⟩ := WsB.EIG.exists_eigen_add_image M₀ B hlin hsymm hpos Ω hΩM hΩsymm c z hz
  exact ⟨k, hk, x, hx, hkeig, hzx⟩

end
end S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian
end P2MW
export P2MW.S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian (solution)
