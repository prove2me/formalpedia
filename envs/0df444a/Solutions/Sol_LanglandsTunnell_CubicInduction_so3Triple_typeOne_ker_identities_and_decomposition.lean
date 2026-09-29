-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.so3Triple_typeOne_ker_identities_and_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7db45824-873c-563b-8948-1e561398fbc9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition

set_option autoImplicit false

namespace KSpec

noncomputable section

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

section SO3

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem cube_eq_neg (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    ∀ f ∈ F, J₃ (J₃ (J₃ f)) = -J₃ f := by
  classical

  have hB0 : ∀ y ∈ F, B 0 y = 0 := fun y hy => form_zero_left F B hlin hy
  have hBsmul : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B (z • x) y = z * B x y := fun z x hx y hy => by
    have h := hlin z x hx 0 F.zero_mem y hy
    rw [add_zero, hB0 y hy, add_zero] at h; exact h
  have hBadd : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ + x₂) y = B x₁ y + B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin 1 x₁ h₁ x₂ h₂ y hy
    rw [one_smul, one_mul] at h; exact h
  have hBsub : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ - x₂) y = B x₁ y - B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin (-1) x₂ h₂ x₁ h₁ y hy
    rw [neg_one_smul, neg_add_eq_sub] at h; rw [h]; ring
  have hBsmul' : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B x (z • y) = (starRingEnd ℂ) z * B x y := fun z x hx y hy => by
    rw [hsymm _ (F.smul_mem z hy) x hx, hBsmul z y hy x hx, map_mul, ← hsymm y hy x hx]
  have hBadd' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ + y₂) = B x y₁ + B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.add_mem h₁ h₂) x hx, hBadd y₁ h₁ y₂ h₂ x hx, map_add, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBsub' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ - y₂) = B x y₁ - B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.sub_mem h₁ h₂) x hx, hBsub y₁ h₁ y₂ h₂ x hx, map_sub, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBself : ∀ w ∈ F, B w w = ((B w w).re : ℂ) := fun w hw => by
    have h := hsymm w hw w hw
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  have hBre_nonneg : ∀ w ∈ F, 0 ≤ (B w w).re := fun w hw => by
    by_cases h0 : w = 0
    · rw [h0, hB0 0 F.zero_mem]; simp
    · exact (hpos w hw h0).le

  let L : Module.End ℂ V := Complex.I • J₃
  let Xp : Module.End ℂ V := J₁ + Complex.I • J₂
  let Xm : Module.End ℂ V := J₁ - Complex.I • J₂
  have hLF : ∀ f ∈ F, L f ∈ F := fun f hf => F.smul_mem _ (hF₃ f hf)
  have hXpF : ∀ f ∈ F, Xp f ∈ F := fun f hf => F.add_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hXmF : ∀ f ∈ F, Xm f ∈ F := fun f hf => F.sub_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hL_apply : ∀ f, L f = Complex.I • J₃ f := fun f => rfl
  have hXp_apply : ∀ f, Xp f = J₁ f + Complex.I • J₂ f := fun f => rfl
  have hXm_apply : ∀ f, Xm f = J₁ f - Complex.I • J₂ f := fun f => rfl

  have hLsymm : ∀ w ∈ F, ∀ w' ∈ F, B (L w) w' = B w (L w') := fun w hw w' hw' => by
    rw [hL_apply, hL_apply, hBsmul _ _ (hF₃ w hw) _ hw', hBsmul' _ _ hw _ (hF₃ w' hw'), hskew₃ w hw w' hw', Complex.conj_I]
    ring

  have hLXp : ∀ f ∈ F, L (Xp f) - Xp (L f) = Xp f := fun f hf => by
    simp only [hL_apply, hXp_apply, map_add, map_smul, smul_add, smul_sub, smul_smul, Complex.I_mul_I]
    have e1 := h31 f hf
    have e2 := h23 f hf

    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← e1]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← e2]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul]
    abel
  have hLXm : ∀ f ∈ F, L (Xm f) - Xm (L f) = -Xm f := fun f hf => by
    simp only [hL_apply, hXm_apply, map_sub, map_smul, smul_sub, smul_smul, Complex.I_mul_I]
    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← h31 f hf]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← h23 f hf]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul, neg_sub]
    abel

  have hJ3L : ∀ f, J₃ f = (-Complex.I) • L f := fun f => by
    rw [hL_apply, smul_smul]; simp
  have hXmXp : ∀ f ∈ F, Xm (Xp f) = L (L f) + L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_add, map_smul, smul_add, hL_apply, smul_smul, Complex.I_mul_I]

    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, sub_smul, neg_one_smul]
    linear_combination (norm := module) hJJ
  have hXpXm : ∀ f ∈ F, Xp (Xm f) = L (L f) - L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_sub, map_smul, smul_sub, hL_apply, smul_smul, Complex.I_mul_I]
    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, neg_one_smul]
    linear_combination (norm := module) hJJ

  have hadjp : ∀ w ∈ F, ∀ y ∈ F, B (Xp w) y = -B w (Xm y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBadd _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBsub' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring
  have hadjm : ∀ w ∈ F, ∀ y ∈ F, B (Xm w) y = -B w (Xp y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBsub _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBadd' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring

  have hbound : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w →
      μ = (μ.re : ℂ) ∧ (μ.re + 2) * (μ.re - 1) ≤ 0 ∧ (μ.re - 2) * (μ.re + 1) ≤ 0 := by
    intro w hw hw0 μ hμ
    have hp : 0 < (B w w).re := hpos w hw hw0

    have hreal : μ = (μ.re : ℂ) := by
      have h1 : B (L w) w = μ * B w w := by rw [hμ, hBsmul μ w hw w hw]
      have h2 : B (L w) w = (starRingEnd ℂ) μ * B w w := by rw [hLsymm w hw w hw, hμ, hBsmul' μ w hw w hw]
      have h3 : (μ - (starRingEnd ℂ) μ) * B w w = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
      have hB0' : B w w ≠ 0 := by
        intro h; rw [h, Complex.zero_re] at hp; exact lt_irrefl _ hp
      have h4 : μ = (starRingEnd ℂ) μ := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hB0')
      exact (Complex.conj_eq_iff_re.1 h4.symm).symm
    refine ⟨hreal, ?_, ?_⟩
    ·
      have hXw := hXpF w hw
      have h1 : B (Xp w) (Xp w) = -((starRingEnd ℂ) (μ * μ + μ - 2) * B w w) := by
        rw [hadjp w hw _ hXw, hXmXp w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w + μ • w - (2 : ℂ) • w = (μ * μ + μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
        Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re + μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]
    · have hXw := hXmF w hw
      have h1 : B (Xm w) (Xm w) = -((starRingEnd ℂ) (μ * μ - μ - 2) * B w w) := by
        rw [hadjm w hw _ hXw, hXpXm w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w - μ • w - (2 : ℂ) • w = (μ * μ - μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.mul_im, mul_zero, zero_mul, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re - μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]

  have hspec : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w → μ * (μ * μ - 1) = 0 := by
    intro w hw hw0 μ hμ
    obtain ⟨hreal, hb1, hb2⟩ := hbound w hw hw0 μ hμ
    set r : ℝ := μ.re with hr

    have hup : L (Xp w) = (μ + 1) • Xp w := by
      have h := hLXp w hw
      rw [sub_eq_iff_eq_add] at h
      rw [h, hμ, map_smul, add_smul, one_smul, add_comm]
    have hr_le : r ≤ 0 ∨ r = 1 := by
      by_cases hX : Xp w = 0
      ·
        have h0 : (μ * μ + μ - 2) • w = 0 := by
          have h := hXmXp w hw
          rw [hX, map_zero] at h
          have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
          rw [hLLw, hμ] at h
          rw [show (μ * μ + μ - 2) • w = (μ * μ) • w + μ • w - (2 : ℂ) • w from by module]
          exact h.symm
        have hsc : μ * μ + μ - 2 = 0 := (smul_eq_zero.1 h0).resolve_right hw0
        rw [hreal] at hsc
        have : r * r + r - 2 = 0 := by exact_mod_cast hsc
        right; nlinarith [this, hb2]
      · obtain ⟨-, hb1', -⟩ := hbound _ (hXpF w hw) hX (μ + 1) hup
        left
        have : (μ + 1).re = r + 1 := by rw [Complex.add_re, Complex.one_re]
        rw [this] at hb1'
        nlinarith [hb1', hb1]

    have hdown : L (Xm w) = (μ - 1) • Xm w := by
      have h := hLXm w hw
      rw [sub_eq_iff_eq_add] at h
      rw [h, hμ, map_smul, sub_smul, one_smul]; abel
    have hr_ge : 0 ≤ r ∨ r = -1 := by
      by_cases hX : Xm w = 0
      · have h0 : (μ * μ - μ - 2) • w = 0 := by
          have h := hXpXm w hw
          rw [hX, map_zero] at h
          have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
          rw [hLLw, hμ] at h
          rw [show (μ * μ - μ - 2) • w = (μ * μ) • w - μ • w - (2 : ℂ) • w from by module]
          exact h.symm
        have hsc : μ * μ - μ - 2 = 0 := (smul_eq_zero.1 h0).resolve_right hw0
        rw [hreal] at hsc
        have : r * r - r - 2 = 0 := by exact_mod_cast hsc
        right; nlinarith [this, hb1]
      · obtain ⟨-, -, hb2'⟩ := hbound _ (hXmF w hw) hX (μ - 1) hdown
        left
        have : (μ - 1).re = r - 1 := by rw [Complex.sub_re, Complex.one_re]
        rw [this] at hb2'
        nlinarith [hb2', hb2]
    have hr3 : r * (r * r - 1) = 0 := by
      rcases hr_le with h1 | h1 <;> rcases hr_ge with h2 | h2
      · have : r = 0 := le_antisymm h1 h2
        rw [this]; ring
      · rw [h2]; ring
      · rw [h1]; ring
      · rw [h1]; ring
    rw [hreal]; exact_mod_cast hr3

  intro f hf
  obtain ⟨s, g, hg, hfsum⟩ := exists_eigen_decomposition (Module.finrank ℂ F) F rfl B hlin hsymm hpos L hLF hLsymm f hf

  have hL3 : L (L (L f)) = L f := by
    rw [hfsum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    obtain ⟨hgF, hgeig⟩ := hg μ hμ
    by_cases h0 : g μ = 0
    · simp [h0]
    · have hsp := hspec (g μ) hgF h0 μ hgeig
      rw [hgeig, map_smul, hgeig, map_smul, map_smul, hgeig, smul_smul, smul_smul]
      have : μ * μ * μ = μ := by linear_combination hsp
      rw [this]

  have h1 : J₃ (J₃ (J₃ f)) = Complex.I • L (L (L f)) := by
    rw [hJ3L (J₃ (J₃ f)), hJ3L (J₃ f), hJ3L f, map_smul, map_smul, map_smul, smul_smul, smul_smul]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-Complex.I) * hI
  rw [h1, hL3, hJ3L f, neg_smul, neg_neg]

theorem triplet (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    (∀ h ∈ F, J₃ h = 0 → J₁ (J₁ h) = -h ∧ J₂ (J₂ h) = -h ∧ J₁ (J₂ h) = 0 ∧ J₂ (J₁ h) = 0) ∧
    (∀ x ∈ F, J₃ (J₂ (J₃ (J₃ x))) = 0 ∧ J₃ (J₁ (J₃ (J₃ x))) = 0 ∧ J₃ (x + J₃ (J₃ x)) = 0 ∧
      x = J₂ (J₂ (J₃ (J₃ x))) + J₁ (J₁ (J₃ (J₃ x))) + (x + J₃ (J₃ x))) := by
  have hcube := cube_eq_neg F J₁ J₂ J₃ hF₁ hF₂ hF₃ h12 h23 h31 hcas B hlin hsymm hpos hskew₁ hskew₂ hskew₃
  classical

  have hB0 : ∀ y ∈ F, B 0 y = 0 := fun y hy => form_zero_left F B hlin hy
  have hBsmul : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B (z • x) y = z * B x y := fun z x hx y hy => by
    have h := hlin z x hx 0 F.zero_mem y hy
    rw [add_zero, hB0 y hy, add_zero] at h; exact h
  have hBadd : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ + x₂) y = B x₁ y + B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin 1 x₁ h₁ x₂ h₂ y hy
    rw [one_smul, one_mul] at h; exact h
  have hBsub : ∀ x₁ ∈ F, ∀ x₂ ∈ F, ∀ y ∈ F, B (x₁ - x₂) y = B x₁ y - B x₂ y := fun x₁ h₁ x₂ h₂ y hy => by
    have h := hlin (-1) x₂ h₂ x₁ h₁ y hy
    rw [neg_one_smul, neg_add_eq_sub] at h; rw [h]; ring
  have hBsmul' : ∀ (z : ℂ), ∀ x ∈ F, ∀ y ∈ F, B x (z • y) = (starRingEnd ℂ) z * B x y := fun z x hx y hy => by
    rw [hsymm _ (F.smul_mem z hy) x hx, hBsmul z y hy x hx, map_mul, ← hsymm y hy x hx]
  have hBadd' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ + y₂) = B x y₁ + B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.add_mem h₁ h₂) x hx, hBadd y₁ h₁ y₂ h₂ x hx, map_add, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBsub' : ∀ x ∈ F, ∀ y₁ ∈ F, ∀ y₂ ∈ F, B x (y₁ - y₂) = B x y₁ - B x y₂ := fun x hx y₁ h₁ y₂ h₂ => by
    rw [hsymm _ (F.sub_mem h₁ h₂) x hx, hBsub y₁ h₁ y₂ h₂ x hx, map_sub, ← hsymm y₁ h₁ x hx, ← hsymm y₂ h₂ x hx]
  have hBself : ∀ w ∈ F, B w w = ((B w w).re : ℂ) := fun w hw => by
    have h := hsymm w hw w hw
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  have hBre_nonneg : ∀ w ∈ F, 0 ≤ (B w w).re := fun w hw => by
    by_cases h0 : w = 0
    · rw [h0, hB0 0 F.zero_mem]; simp
    · exact (hpos w hw h0).le

  let L : Module.End ℂ V := Complex.I • J₃
  let Xp : Module.End ℂ V := J₁ + Complex.I • J₂
  let Xm : Module.End ℂ V := J₁ - Complex.I • J₂
  have hLF : ∀ f ∈ F, L f ∈ F := fun f hf => F.smul_mem _ (hF₃ f hf)
  have hXpF : ∀ f ∈ F, Xp f ∈ F := fun f hf => F.add_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hXmF : ∀ f ∈ F, Xm f ∈ F := fun f hf => F.sub_mem (hF₁ f hf) (F.smul_mem _ (hF₂ f hf))
  have hL_apply : ∀ f, L f = Complex.I • J₃ f := fun f => rfl
  have hXp_apply : ∀ f, Xp f = J₁ f + Complex.I • J₂ f := fun f => rfl
  have hXm_apply : ∀ f, Xm f = J₁ f - Complex.I • J₂ f := fun f => rfl

  have hLsymm : ∀ w ∈ F, ∀ w' ∈ F, B (L w) w' = B w (L w') := fun w hw w' hw' => by
    rw [hL_apply, hL_apply, hBsmul _ _ (hF₃ w hw) _ hw', hBsmul' _ _ hw _ (hF₃ w' hw'), hskew₃ w hw w' hw', Complex.conj_I]
    ring

  have hLXp : ∀ f ∈ F, L (Xp f) - Xp (L f) = Xp f := fun f hf => by
    simp only [hL_apply, hXp_apply, map_add, map_smul, smul_add, smul_sub, smul_smul, Complex.I_mul_I]
    have e1 := h31 f hf
    have e2 := h23 f hf

    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← e1]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← e2]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul]
    abel
  have hLXm : ∀ f ∈ F, L (Xm f) - Xm (L f) = -Xm f := fun f hf => by
    simp only [hL_apply, hXm_apply, map_sub, map_smul, smul_sub, smul_smul, Complex.I_mul_I]
    have e1' : J₃ (J₁ f) = J₂ f + J₁ (J₃ f) := by rw [← h31 f hf]; abel
    have e2' : J₃ (J₂ f) = J₂ (J₃ f) - J₁ f := by rw [← h23 f hf]; abel
    rw [e1', e2']
    simp only [smul_add, smul_sub, neg_one_smul, neg_sub]
    abel

  have hJ3L : ∀ f, J₃ f = (-Complex.I) • L f := fun f => by
    rw [hL_apply, smul_smul]; simp
  have hXmXp : ∀ f ∈ F, Xm (Xp f) = L (L f) + L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_add, map_smul, smul_add, hL_apply, smul_smul, Complex.I_mul_I]

    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, sub_smul, neg_one_smul]
    linear_combination (norm := module) hJJ
  have hXpXm : ∀ f ∈ F, Xp (Xm f) = L (L f) - L f - (2 : ℂ) • f := fun f hf => by
    have hc := hcas f hf
    simp only [hXm_apply, hXp_apply, map_sub, map_smul, smul_sub, hL_apply, smul_smul, Complex.I_mul_I]
    have e12 : J₁ (J₂ f) = J₃ f + J₂ (J₁ f) := by rw [← h12 f hf]; abel
    have hJJ : J₁ (J₁ f) + J₂ (J₂ f) = (-2 : ℂ) • f - J₃ (J₃ f) := by rw [← hc]; abel
    rw [e12]
    simp only [smul_add, neg_one_smul]
    linear_combination (norm := module) hJJ

  have hadjp : ∀ w ∈ F, ∀ y ∈ F, B (Xp w) y = -B w (Xm y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBadd _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBsub' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring
  have hadjm : ∀ w ∈ F, ∀ y ∈ F, B (Xm w) y = -B w (Xp y) := fun w hw y hy => by
    rw [hXp_apply, hXm_apply, hBsub _ (hF₁ w hw) _ (F.smul_mem _ (hF₂ w hw)) y hy,
      hBsmul _ _ (hF₂ w hw) y hy, hskew₁ w hw y hy, hskew₂ w hw y hy,
      hBadd' w hw _ (hF₁ y hy) _ (F.smul_mem _ (hF₂ y hy)), hBsmul' _ w hw _ (hF₂ y hy), Complex.conj_I]
    ring

  have hbound : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w →
      μ = (μ.re : ℂ) ∧ (μ.re + 2) * (μ.re - 1) ≤ 0 ∧ (μ.re - 2) * (μ.re + 1) ≤ 0 := by
    intro w hw hw0 μ hμ
    have hp : 0 < (B w w).re := hpos w hw hw0

    have hreal : μ = (μ.re : ℂ) := by
      have h1 : B (L w) w = μ * B w w := by rw [hμ, hBsmul μ w hw w hw]
      have h2 : B (L w) w = (starRingEnd ℂ) μ * B w w := by rw [hLsymm w hw w hw, hμ, hBsmul' μ w hw w hw]
      have h3 : (μ - (starRingEnd ℂ) μ) * B w w = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
      have hB0' : B w w ≠ 0 := by
        intro h; rw [h, Complex.zero_re] at hp; exact lt_irrefl _ hp
      have h4 : μ = (starRingEnd ℂ) μ := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hB0')
      exact (Complex.conj_eq_iff_re.1 h4.symm).symm
    refine ⟨hreal, ?_, ?_⟩
    ·
      have hXw := hXpF w hw
      have h1 : B (Xp w) (Xp w) = -((starRingEnd ℂ) (μ * μ + μ - 2) * B w w) := by
        rw [hadjp w hw _ hXw, hXmXp w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w + μ • w - (2 : ℂ) • w = (μ * μ + μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
        Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re + μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]
    · have hXw := hXmF w hw
      have h1 : B (Xm w) (Xm w) = -((starRingEnd ℂ) (μ * μ - μ - 2) * B w w) := by
        rw [hadjm w hw _ hXw, hXpXm w hw]
        have hLLw : L (L w) = (μ * μ) • w := by rw [hμ, map_smul, hμ, smul_smul]
        rw [hLLw, hμ, show (μ * μ) • w - μ • w - (2 : ℂ) • w = (μ * μ - μ - 2) • w from by module,
          hBsmul' _ w hw w hw]
      have h2 := hBre_nonneg _ hXw
      rw [h1, hreal] at h2
      simp only [map_sub, map_mul, Complex.conj_ofReal, map_ofNat, Complex.neg_re, Complex.mul_re,
        Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.mul_im, mul_zero, zero_mul, sub_zero, zero_add] at h2
      rw [hBself w hw] at h2
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2
      have h2' : 0 ≤ -((μ.re * μ.re - μ.re - 2) * (B w w).re) := by simpa using h2
      nlinarith [h2', hp]

  have hXpE : ∀ g ∈ F, L g = (1 : ℂ) • g → Xp g = 0 := by
    intro g hg hLg
    by_contra hne
    have hup : L (Xp g) = ((1 : ℂ) + 1) • Xp g := by
      have h := hLXp g hg
      rw [sub_eq_iff_eq_add] at h
      rw [h, hLg, map_smul, add_smul, one_smul, add_comm]
    obtain ⟨-, hb, -⟩ := hbound _ (hXpF g hg) hne _ hup
    norm_num at hb
  have hXmE : ∀ g ∈ F, L g = (-1 : ℂ) • g → Xm g = 0 := by
    intro g hg hLg
    by_contra hne
    have hdown : L (Xm g) = ((-1 : ℂ) - 1) • Xm g := by
      have h := hLXm g hg
      rw [sub_eq_iff_eq_add] at h
      rw [h, hLg, map_smul, sub_smul, one_smul]; abel
    obtain ⟨-, -, hb⟩ := hbound _ (hXmF g hg) hne _ hdown
    norm_num at hb
  have hspec' : ∀ g ∈ F, g ≠ 0 → ∀ μ : ℂ, L g = μ • g → μ = -1 ∨ μ = 0 ∨ μ = 1 := by

    intro g hg hg0 μ hμ
    have h3 : L (L (L g)) = L g := by
      rw [hL_apply, hL_apply, hL_apply, map_smul, map_smul, map_smul, smul_smul, smul_smul, hcube g hg, smul_neg]
      have hI3 : Complex.I * Complex.I * Complex.I = -Complex.I := by rw [Complex.I_mul_I]; ring
      rw [hI3, neg_smul, neg_neg]
    rw [hμ, map_smul, hμ, map_smul, map_smul, hμ, smul_smul, smul_smul] at h3
    have h4 : (μ * μ * μ - μ) • g = 0 := by rw [sub_smul, h3, sub_self]
    have h5 : μ * μ * μ - μ = 0 := (smul_eq_zero.1 h4).resolve_right hg0
    have h6 : μ * (μ - 1) * (μ + 1) = 0 := by linear_combination h5
    rcases mul_eq_zero.1 h6 with h7 | h7
    · rcases mul_eq_zero.1 h7 with h8 | h8
      · exact Or.inr (Or.inl h8)
      · exact Or.inr (Or.inr (sub_eq_zero.1 h8))
    · exact Or.inl (eq_neg_of_add_eq_zero_left h7)
  refine ⟨?_, ?_⟩

  · intro h hh h3
    have hJ2h := hF₂ h hh
    have hJ1h := hF₁ h hh
    have hy : J₁ (J₂ h) = J₂ (J₁ h) := by
      have := h12 h hh; rw [h3] at this; exact sub_eq_zero.1 this
    have h32 : J₃ (J₂ h) = -J₁ h := by
      have := h23 h hh; rw [h3, map_zero] at this
      linear_combination (norm := module) (-1 : ℂ) • this
    have h31' : J₃ (J₁ h) = J₂ h := by
      have := h31 h hh; rw [h3, map_zero, sub_zero] at this; exact this
    have hcas' : J₁ (J₁ h) = (-2 : ℂ) • h - J₂ (J₂ h) := by
      have := hcas h hh; rw [h3, map_zero, add_zero] at this
      linear_combination (norm := module) this

    have hz3 : J₃ (J₂ (J₂ h) + h) = (-2 : ℂ) • J₂ (J₁ h) := by
      have e := h23 (J₂ h) hJ2h
      rw [map_add, h3, add_zero]
      have : J₃ (J₂ (J₂ h)) = J₂ (J₃ (J₂ h)) - J₁ (J₂ h) := by rw [← e]; abel
      rw [this, h32, map_neg, hy]; module
    have hy3 : J₃ (J₂ (J₁ h)) = (2 : ℂ) • (J₂ (J₂ h) + h) := by
      have e := h23 (J₁ h) hJ1h
      have : J₃ (J₂ (J₁ h)) = J₂ (J₃ (J₁ h)) - J₁ (J₁ h) := by rw [← e]; abel
      rw [this, h31', hcas']; module

    have hzF : J₂ (J₂ h) + h ∈ F := F.add_mem (hF₂ _ hJ2h) hh
    have hzz : J₃ (J₃ (J₂ (J₂ h) + h)) = (-4 : ℂ) • (J₂ (J₂ h) + h) := by
      rw [hz3, map_smul, hy3, smul_smul]; norm_num
    have hz0 : J₂ (J₂ h) + h = 0 := by
      have hc := hcube _ hzF
      rw [hzz, map_smul] at hc

      have hJz : J₃ (J₂ (J₂ h) + h) = 0 := by
        have : ((-4 : ℂ) + 1) • J₃ (J₂ (J₂ h) + h) = 0 := by rw [add_smul, one_smul, hc, neg_add_cancel]
        exact (smul_eq_zero.1 this).resolve_left (by norm_num)
      have : (-4 : ℂ) • (J₂ (J₂ h) + h) = 0 := by rw [← hzz, hJz, map_zero]
      exact (smul_eq_zero.1 this).resolve_left (by norm_num)
    have hy0 : J₂ (J₁ h) = 0 := by
      have : (2 : ℂ) • (J₂ (J₂ h) + h) = 0 := by rw [hz0, smul_zero]
      rw [← hy3] at this
      have : (-2 : ℂ) • J₂ (J₁ h) = 0 := by rw [← hz3, hz0, map_zero]
      exact (smul_eq_zero.1 this).resolve_left (by norm_num)
    have hJ22 : J₂ (J₂ h) = -h := eq_neg_of_add_eq_zero_left hz0
    refine ⟨?_, hJ22, by rw [hy, hy0], hy0⟩
    rw [hcas', hJ22]; module

  · intro x hx
    have hJ3x := hF₃ x hx
    have hJ33x := hF₃ _ hJ3x

    have hC : ∀ x ∈ F, J₂ (J₃ x) + J₁ (J₃ (J₃ x)) = 0 ∧ J₁ (J₃ x) - J₂ (J₃ (J₃ x)) = 0 := by
      intro x hx
      obtain ⟨s, g, hg, hxsum⟩ := exists_eigen_decomposition (Module.finrank ℂ F) F rfl B hlin hsymm hpos L hLF hLsymm x hx
      have key' : ∀ w ∈ F, w ≠ 0 → ∀ μ : ℂ, L w = μ • w →
          J₂ (J₃ w) + J₁ (J₃ (J₃ w)) = 0 ∧ J₁ (J₃ w) - J₂ (J₃ (J₃ w)) = 0 := by
        intro w hwF hw0 μ hge
        have hJg : J₃ w = (-Complex.I * μ) • w := by rw [hJ3L, hge, smul_smul]
        have hJJg : J₃ (J₃ w) = (-(μ * μ)) • w := by
          rw [hJg, map_smul, hJg, smul_smul]; congr 1
          have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination (μ * μ) * hI
        rw [hJJg, hJg, map_smul, map_smul, map_smul, map_smul]
        rcases hspec' w hwF hw0 μ hge with rfl | rfl | rfl
        ·
          have hm := hXmE w hwF hge
          rw [hXm_apply] at hm
          have hJ1 : J₁ w = Complex.I • J₂ w := by rw [← sub_eq_zero]; exact hm
          have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
          constructor
          · rw [hJ1, smul_smul]; module
          · rw [hJ1, smul_smul, show (-Complex.I * -1 * Complex.I : ℂ) = -1 from by linear_combination hI]; module
        · simp
        ·
          have hp := hXpE w hwF hge
          rw [hXp_apply] at hp
          have hJ1 : J₁ w = -(Complex.I • J₂ w) := eq_neg_of_add_eq_zero_left hp
          have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
          constructor
          · rw [hJ1, smul_neg, smul_smul]; module
          · rw [hJ1, smul_neg, smul_smul, show (-Complex.I * 1 * Complex.I : ℂ) = 1 from by linear_combination (-1 : ℂ) * hI]
            module
      have key : ∀ μ ∈ s, J₂ (J₃ (g μ)) + J₁ (J₃ (J₃ (g μ))) = 0 ∧ J₁ (J₃ (g μ)) - J₂ (J₃ (J₃ (g μ))) = 0 := by
        intro μ hμ
        obtain ⟨hgF, hge⟩ := hg μ hμ
        by_cases h0 : g μ = 0
        · simp [h0]
        · exact key' (g μ) hgF h0 μ hge
      constructor
      · rw [hxsum]; simp only [map_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun μ hμ => (key μ hμ).1
      · rw [hxsum]; simp only [map_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_eq_zero fun μ hμ => (key μ hμ).2
    have hJ333 : J₃ (J₃ (J₃ x)) = -J₃ x := hcube x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      have e := h23 (J₃ (J₃ x)) hJ33x
      have : J₃ (J₂ (J₃ (J₃ x))) = J₂ (J₃ (J₃ (J₃ x))) - J₁ (J₃ (J₃ x)) := by rw [← e]; abel
      rw [this, hJ333, map_neg]
      have := (hC x hx).1
      linear_combination (norm := module) (-1 : ℂ) • this
    ·
      have e := h31 (J₃ (J₃ x)) hJ33x
      have : J₃ (J₁ (J₃ (J₃ x))) = J₁ (J₃ (J₃ (J₃ x))) + J₂ (J₃ (J₃ x)) := by rw [← e]; abel
      rw [this, hJ333, map_neg]
      have := (hC x hx).2
      linear_combination (norm := module) (-1 : ℂ) • this
    ·
      rw [map_add, hJ333, add_neg_cancel]
    ·
      have hc := hcas (J₃ (J₃ x)) hJ33x
      rw [hJ333, map_neg] at hc

      linear_combination (norm := module) (-1 : ℂ) • hc

end SO3

theorem fin3_cases' (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp

section TripletBasis

open Module

theorem exists_tripletBasis
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hrel₁ : ∀ x : W, ρ 0 1 (ρ 0 2 x) - ρ 0 2 (ρ 0 1 x) = -ρ 1 2 x)
    (hrel₂ : ∀ x : W, ρ 0 1 (ρ 1 2 x) - ρ 1 2 (ρ 0 1 x) = ρ 0 2 x)
    (hrel₃ : ∀ x : W, ρ 0 2 (ρ 1 2 x) - ρ 1 2 (ρ 0 2 x) = -ρ 0 1 x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y)) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m × Fin 3) ℂ W), ∀ (i j : Fin 3) (t : Fin m) (c : Fin 3),
      ρ i j (b (t, c)) = ∑ d : Fin 3, ((Matrix.single i j (1 : ℂ) - Matrix.single j i 1 : Matrix (Fin 3) (Fin 3) ℂ) d c) • b (t, d) := by
  classical

  set J₁ := ρ 1 2 with hJ₁
  set J₂ := ρ 0 2 with hJ₂
  set J₃ := ρ 0 1 with hJ₃
  have h12 : ∀ f ∈ (⊤ : Submodule ℂ W), J₁ (J₂ f) - J₂ (J₁ f) = J₃ f := fun f _ => by
    have := hrel₃ f; rw [hJ₁, hJ₂, hJ₃]; linear_combination (norm := module) (-1 : ℂ) • this
  have h23 : ∀ f ∈ (⊤ : Submodule ℂ W), J₂ (J₃ f) - J₃ (J₂ f) = J₁ f := fun f _ => by
    have := hrel₁ f; rw [hJ₁, hJ₂, hJ₃]; linear_combination (norm := module) (-1 : ℂ) • this
  have h31 : ∀ f ∈ (⊤ : Submodule ℂ W), J₃ (J₁ f) - J₁ (J₃ f) = J₂ f := fun f _ => by
    have := hrel₂ f; rw [hJ₁, hJ₂, hJ₃]; exact this
  have hcas' : ∀ f ∈ (⊤ : Submodule ℂ W), J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f := fun f _ => by
    have := hcas f; rw [hJ₁, hJ₂, hJ₃]; linear_combination (norm := module) this
  have hT := triplet (⊤ : Submodule ℂ W) J₁ J₂ J₃ (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) h12 h23 h31 hcas' B (fun z w₁ _ w₂ _ w' _ => hlin z w₁ w₂ w')
    (fun w _ w' _ => hsymm w w') (fun w _ hw => hpos w hw)
    (fun x _ y _ => by rw [hJ₁]; exact hskew 1 2 x y) (fun x _ y _ => by rw [hJ₂]; exact hskew 0 2 x y)
    (fun x _ y _ => by rw [hJ₃]; exact hskew 0 1 x y)
  obtain ⟨hT1, hT2⟩ := hT

  have hker : ∀ h : W, J₃ h = 0 →
      J₁ (J₁ h) = -h ∧ J₂ (J₂ h) = -h ∧ J₁ (J₂ h) = 0 ∧ J₂ (J₁ h) = 0 ∧ J₃ (J₂ h) = -J₁ h ∧ J₃ (J₁ h) = J₂ h :=
    fun h h3 => by
    obtain ⟨a, b', c, d⟩ := hT1 h Submodule.mem_top h3
    refine ⟨a, b', c, d, ?_, ?_⟩
    · have := h23 h Submodule.mem_top; rw [h3, map_zero] at this
      linear_combination (norm := module) (-1 : ℂ) • this
    · have := h31 h Submodule.mem_top; rw [h3, map_zero, sub_zero] at this; exact this

  let Kr : Submodule ℂ W := LinearMap.ker J₃
  let bK := Module.finBasis ℂ Kr
  let m := Module.finrank ℂ Kr
  let hv : Fin m → W := fun t => (bK t : W)
  have hv3 : ∀ t, J₃ (hv t) = 0 := fun t => (bK t).2

  let v : Fin m × Fin 3 → W := fun tc => if tc.2 = 0 then J₂ (hv tc.1) else if tc.2 = 1 then J₁ (hv tc.1) else hv tc.1
  have v0 : ∀ t, v (t, 0) = J₂ (hv t) := fun t => rfl
  have v1 : ∀ t, v (t, 1) = J₁ (hv t) := fun t => rfl
  have v2 : ∀ t, v (t, 2) = hv t := fun t => rfl

  have hsum : ∀ g : Fin m × Fin 3 → ℂ, ∑ tc, g tc • v tc =
      J₂ (∑ t, g (t, 0) • hv t) + J₁ (∑ t, g (t, 1) • hv t) + ∑ t, g (t, 2) • hv t := by
    intro g
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three, v0, v1, v2, map_sum, map_smul, Finset.sum_add_distrib]
  have hkerA : ∀ (a : Fin m → ℂ), J₃ (∑ t, a t • hv t) = 0 := fun a => by
    rw [map_sum]; exact Finset.sum_eq_zero fun t _ => by rw [map_smul, hv3, smul_zero]

  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    set A₀ := ∑ t, g (t, 0) • hv t with hA₀
    set A₁ := ∑ t, g (t, 1) • hv t with hA₁
    set A₂ := ∑ t, g (t, 2) • hv t with hA₂
    have k₀ := hker A₀ (hkerA _)
    have k₁ := hker A₁ (hkerA _)
    have k₂ := hker A₂ (hkerA _)

    have e2 : A₂ = 0 := by
      have h := congrArg (fun w => w + J₃ (J₃ w)) hg
      simp only [map_add, map_zero, add_zero] at h
      rw [k₀.2.2.2.2.1, k₁.2.2.2.2.2, map_neg, k₀.2.2.2.2.2, k₁.2.2.2.2.1, hkerA, map_zero] at h

      linear_combination (norm := module) h
    have hg' : J₂ A₀ + J₁ A₁ = 0 := by rw [e2, add_zero] at hg; exact hg
    have e0 : A₀ = 0 := by
      have h := congrArg J₂ hg'
      rw [map_add, k₀.2.1, k₁.2.2.2.1, map_zero, add_zero, neg_eq_zero] at h; exact h
    have e1 : A₁ = 0 := by
      have h := congrArg J₁ hg'
      rw [map_add, k₀.2.2.1, k₁.1, map_zero, zero_add, neg_eq_zero] at h; exact h

    have hind : ∀ (c : Fin 3) (a : Fin m → ℂ), (∑ t, a t • hv t) = 0 → ∀ t, a t = 0 := by
      intro c a ha t
      have : (∑ t, a t • bK t : Kr) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]; exact ha
      exact Fintype.linearIndependent_iff.1 bK.linearIndependent a this t
    rintro ⟨t, c⟩
    rcases KSpec.fin3_cases' c with rfl | rfl | rfl
    · exact hind 0 _ e0 t
    · exact hind 1 _ e1 t
    · exact hind 2 _ e2 t

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro x _
    obtain ⟨h0k, h1k, h2k, hx⟩ := hT2 x Submodule.mem_top

    have hexp : ∀ h : W, J₃ h = 0 → ∃ a : Fin m → ℂ, h = ∑ t, a t • hv t := by
      intro h hh
      refine ⟨fun t => bK.repr ⟨h, hh⟩ t, ?_⟩
      have := congrArg Subtype.val (bK.sum_repr ⟨h, hh⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    obtain ⟨a0, ha0⟩ := hexp _ h0k
    obtain ⟨a1, ha1⟩ := hexp _ h1k
    obtain ⟨a2, ha2⟩ := hexp _ h2k
    rw [hx, ha0, ha1, ha2]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [map_sum]; refine Submodule.sum_mem _ fun t _ => ?_
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(t, 0), v0 t⟩)
    · rw [map_sum]; refine Submodule.sum_mem _ fun t _ => ?_
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(t, 1), v1 t⟩)
    · refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(t, 2), v2 t⟩)
  let b : Module.Basis (Fin m × Fin 3) ℂ W := Module.Basis.mk hli hsp
  have hb : ∀ tc, b tc = v tc := fun tc => Module.Basis.mk_apply hli hsp tc
  refine ⟨m, b, fun i j t c => ?_⟩
  obtain ⟨k11, k22, k12, k21, k32, k31⟩ := hker (hv t) (hv3 t)
  have k3 := hv3 t
  have a10 : ∀ x, ρ 1 0 x = -J₃ x := fun x => by rw [hanti 0 1 x]
  have a20 : ∀ x, ρ 2 0 x = -J₂ x := fun x => by rw [hanti 0 2 x]
  have a21 : ∀ x, ρ 2 1 x = -J₁ x := fun x => by rw [hanti 1 2 x]
  have adiag : ∀ (i : Fin 3) (x : W), ρ i i x = 0 := fun i x => by
    have h := hanti i i x
    have h2 : (2 : ℂ) • ρ i i x = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  have e3 : ∀ x, ρ 0 1 x = J₃ x := fun x => by rw [hJ₃]
  have e2 : ∀ x, ρ 0 2 x = J₂ x := fun x => by rw [hJ₂]
  have e1 : ∀ x, ρ 1 2 x = J₁ x := fun x => by rw [hJ₁]
  fin_cases i <;> fin_cases j <;> fin_cases c <;>
    simp [hb, v0, v1, v2, Fin.sum_univ_three, Matrix.single_apply, adiag, a10, a20, a21, e1, e2, e3,
      k11, k22, k12, k21, k32, k31, k3]

end TripletBasis

end

end KSpec

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℂ V] (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    (∀ h ∈ F, J₃ h = 0 → J₁ (J₁ h) = -h ∧ J₂ (J₂ h) = -h ∧ J₁ (J₂ h) = 0 ∧ J₂ (J₁ h) = 0) ∧
    (∀ x ∈ F, J₃ (J₂ (J₃ (J₃ x))) = 0 ∧ J₃ (J₁ (J₃ (J₃ x))) = 0 ∧ J₃ (x + J₃ (J₃ x)) = 0 ∧
      x = J₂ (J₂ (J₃ (J₃ x))) + J₁ (J₁ (J₃ (J₃ x))) + (x + J₃ (J₃ x))) :=
  KSpec.triplet F J₁ J₂ J₃ hF₁ hF₂ hF₃ h12 h23 h31 hcas B hlin hsymm hpos hskew₁ hskew₂ hskew₃

end S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition (solution)
