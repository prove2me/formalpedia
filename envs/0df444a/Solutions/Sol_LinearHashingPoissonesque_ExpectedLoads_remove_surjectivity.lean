-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.remove_surjectivity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:50.976192+00:00
-- url     : https://prove2.me/submissions/36372747-4a31-474f-b94b-2cfc68c7e15a

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_condAvgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LoadVector

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.RemoveSurj

open LinearHashingPoissonesque.ExpectedLoads

variable {K : Type*} [Field K] [Fintype K]

noncomputable instance instFintypeLin (u ell : ℕ) : Fintype ((Fin u → K) →ₗ[K] (Fin ell → K)) :=
  Fintype.ofFinite _

noncomputable instance instFintypeDual (ell : ℕ) : Fintype (Module.Dual K (Fin ell → K)) :=
  haveI : Finite (Module.Dual K (Fin ell → K)) :=
    Finite.of_injective (fun f : Module.Dual K (Fin ell → K) => (f : (Fin ell → K) → K))
      DFunLike.coe_injective
  Fintype.ofFinite _

open Classical

/-- Extension by zero. -/
noncomputable def zext {u U : ℕ} (hu : u ≤ U) : (Fin u → K) →ₗ[K] (Fin U → K) where
  toFun x j := if h : j.1 < u then x ⟨j.1, h⟩ else 0
  map_add' x y := by
    funext j; by_cases h : j.1 < u <;> simp [h]
  map_smul' c x := by
    funext j; by_cases h : j.1 < u <;> simp [h]

/-- Truncation. -/
def trunc {u U : ℕ} (hu : u ≤ U) : (Fin U → K) →ₗ[K] (Fin u → K) :=
  LinearMap.funLeft K K (Fin.castLE hu)

lemma trunc_zext {u U : ℕ} (hu : u ≤ U) (x : Fin u → K) : trunc hu (zext hu x) = x := by
  funext j
  simp [trunc, zext, LinearMap.funLeft]

lemma zext_injective {u U : ℕ} (hu : u ≤ U) : Function.Injective (zext (K := K) hu) :=
  Function.LeftInverse.injective (trunc_zext hu)

/-- Restriction of linear maps. -/
noncomputable def restr {u U : ℕ} (hu : u ≤ U) (ell : ℕ) :
    ((Fin U → K) →ₗ[K] (Fin ell → K)) →+ ((Fin u → K) →ₗ[K] (Fin ell → K)) :=
  AddMonoidHom.mk' (fun H => H.comp (zext hu)) (fun _ _ => rfl)

lemma restr_surjective {u U : ℕ} (hu : u ≤ U) (ell : ℕ) :
    Function.Surjective (restr (K := K) hu ell) := by
  intro h
  refine ⟨h.comp (trunc hu), ?_⟩
  apply LinearMap.ext
  intro x
  simp [restr, trunc_zext]

lemma sum_restr {u U : ℕ} (hu : u ≤ U) (ell : ℕ) (g : ((Fin u → K) →ₗ[K] (Fin ell → K)) → ℝ) :
    ∑ H, g (restr hu ell H) =
      ((Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => restr hu ell H = 0)).card : ℝ)
        * ∑ h, g h := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := restr hu ell) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have hc : (Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => restr hu ell H = h)).card
      = (Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => restr hu ell H = 0)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range (restr hu ell) (restr_surjective hu ell h)
      ⟨0, map_zero _⟩
  rw [Finset.sum_congr rfl (fun H hH => by rw [(Finset.mem_filter.1 hH).2]), Finset.sum_const, hc]
  simp

lemma avg_restr {u U : ℕ} (hu : u ≤ U) (ell : ℕ) (g : ((Fin u → K) →ₗ[K] (Fin ell → K)) → ℝ) :
    LinMaxLoad.avgLin K (Fin U → K) ell (fun H => g (restr hu ell H)) =
      LinMaxLoad.avgLin K (Fin u → K) ell g := by
  have h1 := sum_restr hu ell g
  have h2 := sum_restr hu ell (fun _ : (Fin u → K) →ₗ[K] (Fin ell → K) => (1:ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at h2
  simp only [LinMaxLoad.avgLin]
  rw [h1]
  have hpos : (0:ℝ) < (Fintype.card ((Fin u → K) →ₗ[K] (Fin ell → K)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [h2]
  have hc : (0:ℝ) < ((Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => restr hu ell H = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨0, by simp⟩
  field_simp

/-- Surjective linear maps (classical decidability, matching `condAvgLin`). -/
noncomputable def Surjs (U ell : ℕ) : Finset ((Fin U → K) →ₗ[K] (Fin ell → K)) :=
  @Finset.filter _ (fun H => Function.Surjective H) (fun _ => Classical.propDecidable _) Finset.univ

/-- Non-surjective linear maps. -/
noncomputable def NSurjs (U ell : ℕ) : Finset ((Fin U → K) →ₗ[K] (Fin ell → K)) :=
  @Finset.filter _ (fun H => ¬ Function.Surjective H) (fun _ => Classical.propDecidable _) Finset.univ

/-- `φ` kills every column of `H`. -/
def ColKilled {U ell : ℕ} (φ : Module.Dual K (Fin ell → K))
    (H : (Fin U → K) →ₗ[K] (Fin ell → K)) : Prop :=
  ∀ i : Fin U, φ (H (Pi.single i 1)) = 0

lemma card_colKilled {U ell : ℕ} (φ : Module.Dual K (Fin ell → K)) :
    (Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => ColKilled φ H)).card
      = Nat.card (LinearMap.ker φ) ^ U := by
  let e : (Fin U → (Fin ell → K)) ≃ₗ[K] ((Fin U → K) →ₗ[K] (Fin ell → K)) :=
    (Pi.basisFun K (Fin U)).constr K
  have key : ∀ c, ColKilled φ (e c) ↔ ∀ i, φ (c i) = 0 := by
    intro c
    unfold ColKilled
    refine forall_congr' (fun i => ?_)
    have := (Pi.basisFun K (Fin U)).constr_basis K c i
    simp only [Pi.basisFun_apply] at this
    simp [e, this]
  rw [← Fintype.card_subtype]
  have e1 : {H : (Fin U → K) →ₗ[K] (Fin ell → K) // ColKilled φ H}
      ≃ {c : Fin U → (Fin ell → K) // ∀ i, φ (c i) = 0} :=
    (e.toEquiv.subtypeEquiv (fun c => (key c).symm)).symm
  rw [Fintype.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun _ (v : Fin ell → K) => φ v = 0)))]
  rw [Fintype.card_pi]
  simp [Nat.card_eq_fintype_card]

lemma two_mul_card_ker_le {ell : ℕ} (φ : Module.Dual K (Fin ell → K)) (hφ : φ ≠ 0) :
    2 * Nat.card (LinearMap.ker φ) ≤ Fintype.card (Fin ell → K) := by
  have hne : (LinearMap.ker φ).toAddSubgroup.index ≠ 1 := by
    intro h
    rw [AddSubgroup.index_eq_one] at h
    apply hφ
    apply LinearMap.ext
    intro x
    have : x ∈ LinearMap.ker φ := by
      have : x ∈ (LinearMap.ker φ).toAddSubgroup := by rw [h]; trivial
      simpa using this
    simpa using this
  have hidx : (LinearMap.ker φ).toAddSubgroup.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have := AddSubgroup.card_mul_index (LinearMap.ker φ).toAddSubgroup
  rw [Nat.card_eq_fintype_card (α := Fin ell → K)] at this
  have h2 : 2 ≤ (LinearMap.ker φ).toAddSubgroup.index := by omega
  calc 2 * Nat.card (LinearMap.ker φ) = Nat.card (LinearMap.ker φ).toAddSubgroup * 2 := by
        rw [mul_comm]; rfl
    _ ≤ Nat.card (LinearMap.ker φ).toAddSubgroup * (LinearMap.ker φ).toAddSubgroup.index :=
        Nat.mul_le_mul_left _ h2
    _ = _ := this

lemma nonsurj_subset {U ell : ℕ} (H : (Fin U → K) →ₗ[K] (Fin ell → K))
    (h : ¬ Function.Surjective H) : ∃ φ : Module.Dual K (Fin ell → K), φ ≠ 0 ∧ ColKilled φ H := by
  have hlt : LinearMap.range H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h'
    exact h (LinearMap.range_eq_top.1 h')
  obtain ⟨φ, hφ, hle⟩ := (LinearMap.range H).exists_le_ker_of_lt_top hlt
  exact ⟨φ, hφ, fun i => by simpa using hle ⟨_, rfl⟩⟩

/-- Counting non-surjective maps: `#nonsurj * 2^U ≤ #Dual * (q^ell)^U`. -/
lemma card_nonsurj {U ell : ℕ} :
    (NSurjs (K := K) U ell).card * 2 ^ U
      ≤ Fintype.card (Module.Dual K (Fin ell → K)) * Fintype.card (Fin ell → K) ^ U := by
  have hsub : NSurjs (K := K) U ell ⊆ (Finset.univ.filter (fun φ : Module.Dual K (Fin ell → K) => φ ≠ 0)).biUnion
        (fun φ => Finset.univ.filter (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => ColKilled φ H)) := by
    intro H hH
    simp only [NSurjs, Finset.mem_filter, Finset.mem_univ, true_and] at hH
    obtain ⟨φ, h1, h2⟩ := nonsurj_subset H hH
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨φ, h1, h2⟩
  refine (Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
  rw [Finset.sum_mul]
  calc _ ≤ ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual K (Fin ell → K) => φ ≠ 0),
        Fintype.card (Fin ell → K) ^ U := by
        refine Finset.sum_le_sum (fun φ hφ => ?_)
        rw [card_colKilled, ← mul_pow]
        have := two_mul_card_ker_le φ (Finset.mem_filter.1 hφ).2
        rw [mul_comm] at this
        exact Nat.pow_le_pow_left this U
    _ ≤ _ := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (by simp))

lemma card_lin (U ell : ℕ) :
    Fintype.card ((Fin U → K) →ₗ[K] (Fin ell → K)) = Fintype.card (Fin ell → K) ^ U := by
  let e : (Fin U → (Fin ell → K)) ≃ₗ[K] ((Fin U → K) →ₗ[K] (Fin ell → K)) :=
    (Pi.basisFun K (Fin U)).constr K
  rw [← Fintype.card_congr e.toEquiv]
  simp

instance instFiniteLoadVector (ell m : ℕ) : Finite (LoadVector (Fin ell → K) m) := by
  refine Finite.of_injective
    (fun w : LoadVector (Fin ell → K) m => fun y => (⟨w.1 y, ?_⟩ : Fin (m + 1))) ?_
  · have := Finset.single_le_sum (f := w.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    have h2 := w.2
    omega
  · intro w w' h
    apply Subtype.ext
    funext y
    simpa using congrFun h y

lemma exists_bound (ell m : ℕ) (f : LoadVector (Fin ell → K) m → NNReal) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w, (f w : ℝ) ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun w => (f w : ℝ))).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun w => (hM ⟨w, rfl⟩).trans (le_max_left _ _)⟩

lemma labelled_restr {u U : ℕ} (hu : u ≤ U) (ell m : ℕ) (S : Finset (Fin u → K))
    (hS : S.card = m) (hT : (S.map ⟨zext hu, zext_injective hu⟩).card = m)
    (H : (Fin U → K) →ₗ[K] (Fin ell → K)) :
    labelledLoads (S.map ⟨zext hu, zext_injective hu⟩) hT H = labelledLoads S hS (restr hu ell H) := by
  apply Subtype.ext
  funext y
  simp only [labelledLoads, binLoad]
  symm
  apply Finset.card_bij (fun a _ => zext hu a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at ha ⊢
    exact ⟨⟨a, ha.1, rfl⟩, ha.2⟩
  · intro a _ b _ hab
    exact zext_injective hu hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at hb
    obtain ⟨⟨a, ha, rfl⟩, h⟩ := hb
    exact ⟨a, by simp only [Finset.mem_filter]; exact ⟨ha, h⟩, rfl⟩

lemma sum_surj_le {U ell : ℕ} (X : ((Fin U → K) →ₗ[K] (Fin ell → K)) → ℝ) (a : ℝ)
    (h : LinMaxLoad.condAvgLin K (Fin U → K) ell (fun h => Function.Surjective h) X ≤ a) :
    ∑ H ∈ Surjs (K := K) U ell, X H ≤ a * (Surjs (K := K) U ell).card := by
  have h' : (∑ H ∈ Surjs (K := K) U ell, X H) / ((Surjs (K := K) U ell).card : ℝ) ≤ a := h
  by_cases h0 : (Surjs (K := K) U ell).card = 0
  · rw [Finset.card_eq_zero] at h0
    rw [h0]; simp
  · have hpos : (0:ℝ) < ((Surjs (K := K) U ell).card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h0
    have := (div_le_iff₀ hpos).1 h'
    linarith

lemma avg_le_of_cond {u U : ℕ} (hu : u ≤ U) (ell m : ℕ) (f : LoadVector (Fin ell → K) m → NNReal)
    (a : ℝ) (ha : 0 ≤ a) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ w, (f w : ℝ) ≤ M)
    (S : Finset (Fin u → K)) (hS : S.card = m)
    (hcond : ∀ (T : Finset (Fin U → K)) (hT : T.card = m),
        LinMaxLoad.condAvgLin K (Fin U → K) ell (fun h => Function.Surjective h)
          (fun h => (f (labelledLoads T hT h) : ℝ)) ≤ a) :
    LinMaxLoad.avgLin K (Fin u → K) ell (fun h => (f (labelledLoads S hS h) : ℝ))
      ≤ a + M * (Fintype.card (Module.Dual K (Fin ell → K)) : ℝ) * (1 / 2 : ℝ) ^ U := by
  have hT : (S.map ⟨zext hu, zext_injective hu⟩).card = m := by simpa using hS
  set X : ((Fin U → K) →ₗ[K] (Fin ell → K)) → ℝ :=
    fun H => (f (labelledLoads (S.map ⟨zext hu, zext_injective hu⟩) hT H) : ℝ) with hX
  have hXr : X = fun H => (fun h => (f (labelledLoads S hS h) : ℝ)) (restr hu ell H) := by
    funext H; simp only [hX, labelled_restr hu ell m S hS hT H]
  rw [← avg_restr hu ell, ← hXr]
  have hsurj := sum_surj_le X a (hcond _ hT)
  simp only [LinMaxLoad.avgLin]
  set N : ℝ := (Fintype.card ((Fin U → K) →ₗ[K] (Fin ell → K)) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set F := Surjs (K := K) U ell with hFdef
  set G := NSurjs (K := K) U ell with hGdef
  have hsplit : ∑ H, X H = ∑ H ∈ F, X H + ∑ H ∈ G, X H :=
    by
      convert (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun H : (Fin U → K) →ₗ[K] (Fin ell → K) => Function.Surjective H) X).symm <;>
      (ext H; simp [hFdef, hGdef, Surjs, NSurjs])
  have hG : ∑ H ∈ G, X H ≤ M * G.card := by
    calc ∑ H ∈ G, X H ≤ ∑ H ∈ G, M := Finset.sum_le_sum (fun H _ => hM _)
      _ = M * G.card := by simp [mul_comm]
  have hFN : (F.card : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast (Finset.card_le_univ F)
  have hGc : (G.card : ℝ) * 2 ^ U ≤ (Fintype.card (Module.Dual K (Fin ell → K)) : ℝ) * N := by
    have := card_nonsurj (K := K) (U := U) (ell := ell)
    rw [← card_lin U ell] at this
    rw [hGdef, hN]
    exact_mod_cast this
  have h2U : (0:ℝ) < 2 ^ U := by positivity
  have hGN : (G.card : ℝ) ≤ (Fintype.card (Module.Dual K (Fin ell → K)) : ℝ) * N * (1 / 2) ^ U := by
    rw [one_div, inv_pow]
    rw [← div_eq_mul_inv, le_div_iff₀ h2U]; exact hGc
  rw [div_le_iff₀ hNpos]
  calc ∑ H, X H ≤ a * F.card + M * G.card := by rw [hsplit]; exact add_le_add hsurj hG
    _ ≤ a * N + M * ((Fintype.card (Module.Dual K (Fin ell → K)) : ℝ) * N * (1 / 2) ^ U) :=
        add_le_add (mul_le_mul_of_nonneg_left hFN ha) (mul_le_mul_of_nonneg_left hGN hM0)
    _ = _ := by ring

end LinearHashingPoissonesque.Dev.RemoveSurj

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.RemoveSurj in
theorem chk_remove_surjectivity (K : Type*) [Field K] [Fintype K]
    (ell m r : ℕ) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (hr : 1 ≤ r) (hrq : r ≤ Fintype.card K ^ ell)
    (f : LoadVector (Fin ell → K) m → NNReal) (a : ℝ) (ha : 0 ≤ a)
    (hgood : Set.Infinite {U : ℕ | ell ≤ U ∧
      ∀ (S : Finset (Fin U → K)) (hS : S.card = m),
        LinMaxLoad.condAvgLin K (Fin U → K) ell
          (fun h => Function.Surjective h)
          (fun h => (f (labelledLoads S hS h) : ℝ)) ≤ a})
    (u : ℕ) (hu : ell ≤ u) (S : Finset (Fin u → K)) (hS : S.card = m) :
    LinMaxLoad.avgLin K (Fin u → K) ell
      (fun h => (f (labelledLoads S hS h) : ℝ)) ≤ a := by
  obtain ⟨M, hM0, hM⟩ := exists_bound ell m f
  set D : ℝ := (Fintype.card (Module.Dual K (Fin ell → K)) : ℝ) with hD
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : 0 < M * D + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (M * D + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨U, hUgood, hUn⟩ := hgood.exists_gt (max n u)
  obtain ⟨_, hcond⟩ := hUgood
  have huU : u ≤ U := (le_max_right _ _).trans hUn.le
  have h1 := avg_le_of_cond huU ell m f a ha M hM0 hM S hS hcond
  have h2 : (1 / 2 : ℝ) ^ U ≤ (1 / 2) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ((le_max_left _ _).trans hUn.le)
  have h3 : M * D * (1 / 2 : ℝ) ^ U ≤ ε := by
    have hMD : 0 ≤ M * D := by positivity
    calc M * D * (1 / 2 : ℝ) ^ U ≤ (M * D + 1) * (1 / 2) ^ n :=
          mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ ≤ (M * D + 1) * (ε / (M * D + 1)) := mul_le_mul_of_nonneg_left hn.le hc.le
      _ = ε := by field_simp
  linarith

end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_remove_surjectivity := @LinearHashingPoissonesque.ExpectedLoads.chk_remove_surjectivity
