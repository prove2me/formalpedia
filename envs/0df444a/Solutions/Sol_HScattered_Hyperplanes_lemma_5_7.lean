-- Prove2me | solution 1 for HScattered.Hyperplanes.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:18:07.495134+00:00
-- url     : https://prove2.me/submissions/95fe330f-b318-477d-8969-38ce0292a649

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

set_option autoImplicit false

open HScattered.Hyperplanes

lemma proj_count (K E : Type*) [Field K] [Finite K] [AddCommGroup E] [Module K E]
    (T : Submodule K E) [Module.Finite K T] :
    Nat.card {Φ : Submodule K E // Module.finrank K Φ = 1 ∧ Φ ≤ T} * (Nat.card K - 1) =
      Nat.card K ^ Module.finrank K T - 1 := by
  have e : Projectivization K T ≃ {Φ : Submodule K E // Module.finrank K Φ = 1 ∧ Φ ≤ T} :=
    (Projectivization.equivSubmodule K T).trans
      { toFun := fun Ψ => ⟨Ψ.1.map T.subtype, by
          refine ⟨?_, Submodule.map_subtype_le T Ψ.1⟩
          exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective T.subtype
            T.injective_subtype Ψ.1)).symm.trans Ψ.2⟩
        invFun := fun Φ => ⟨Φ.1.comap T.subtype, by
          exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe Φ.2.2)).trans Φ.2.1⟩
        left_inv := fun Ψ => Subtype.ext (Submodule.comap_map_eq_of_injective T.injective_subtype _)
        right_inv := fun Φ => Subtype.ext (by
          show Submodule.map T.subtype (Submodule.comap T.subtype Φ.1) = Φ.1
          rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr Φ.2.2) }
  rw [← Nat.card_congr e]
  have h1 := Projectivization.card K T
  have h2 : Nat.card T = Nat.card K ^ Module.finrank K T := Module.natCard_eq_pow_finrank (K := K)
  rw [h2] at h1
  exact h1.symm

lemma hyp_count_ge (K V : Type*) [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) (hr : Module.finrank K S ≤ Module.finrank K V)
    (hS : 0 < Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧ S ≤ W} *
        (Nat.card K - 1) = Nat.card K ^ (Module.finrank K V - Module.finrank K S) - 1 := by
  have e : {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧ S ≤ W} ≃
      {Φ : Submodule K (Module.Dual K V) // Module.finrank K Φ = 1 ∧ Φ ≤ S.dualAnnihilator} :=
    Equiv.subtypeEquiv ((Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
        OrderDual.ofDual) (by
      intro W
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
      have h2 : (Subspace.orderIsoFiniteDimensional (K := K) (V := V)).toEquiv.trans
          OrderDual.ofDual W = W.dualAnnihilator := rfl
      rw [h2, Subspace.dualAnnihilator_le_dualAnnihilator_iff]
      constructor
      · rintro ⟨h1, h3⟩; exact ⟨by omega, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨by omega, h3⟩)
  rw [Nat.card_congr e]
  have := proj_count K (Module.Dual K V) S.dualAnnihilator
  have hf : Module.finrank K S.dualAnnihilator = Module.finrank K V - Module.finrank K S := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq S
    omega
  rw [hf] at this
  exact this

lemma finrank_sup_span_single {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (A : Submodule R M) (v : M) (hv : v ∉ A) :
    Module.finrank R ↥(A ⊔ Submodule.span R {v}) = Module.finrank R A + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ A.zero_mem)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span R {v})
  have h2 : A ⊓ Submodule.span R {v} = ⊥ :=
    disjoint_iff.mp ((Submodule.disjoint_span_singleton' hv0).mpr hv)
  rw [h2, finrank_bot, finrank_span_singleton hv0] at h1
  omega

lemma scat_down {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) (S : Submodule K V)
    (hSh : Module.finrank K S ≤ h) :
    Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ Module.finrank K S := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  obtain ⟨_, hr, hspan, hsc⟩ := hU
  have step : ∀ S : Submodule K V, Module.finrank K S < h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) →
      ∃ S2 : Submodule K V, Module.finrank K S2 = Module.finrank K S + 1 ∧
        Module.finrank K S2 + 1 ≤ Module.finrank F ↥(S2.restrictScalars F ⊓ U) := by
    intro S hS hSU
    have hne : ¬ (U : Set V) ⊆ (S : Set V) := by
      intro hsub
      have : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hsub
      rw [hspan] at this
      have h' : S = ⊤ := top_le_iff.mp this
      have : Module.finrank K S = Module.finrank K V := by rw [h']; simp
      omega
    obtain ⟨v, hvU, hvS⟩ := Set.not_subset.mp hne
    refine ⟨S ⊔ Submodule.span K {v}, ?_, ?_⟩
    · exact finrank_sup_span_single S v hvS
    · rw [finrank_sup_span_single S v hvS]
      have hvA : v ∉ S.restrictScalars F ⊓ U := fun hm => hvS hm.1
      have h1 := finrank_sup_span_single (R := F) (S.restrictScalars F ⊓ U) v hvA
      have hle : (S.restrictScalars F ⊓ U) ⊔ Submodule.span F {v} ≤
          (S ⊔ Submodule.span K {v}).restrictScalars F ⊓ U := by
        apply sup_le
        · exact inf_le_inf_right _ (Submodule.restrictScalars_mono F le_sup_left)
        · rw [Submodule.span_singleton_le_iff_mem]
          exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self v), hvU⟩
      have := Submodule.finrank_mono hle
      omega
  have key : ∀ m : ℕ, ∀ S : Submodule K V, Module.finrank K S + m = h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) → False := by
    intro m
    induction m with
    | zero =>
      intro S hS hSU
      have := hsc S (by omega)
      omega
    | succ m ih =>
      intro S hS hSU
      obtain ⟨S2, h1, h2⟩ := step S (by omega) hSU
      exact ih S2 (by omega) h2
  by_contra hcon
  exact key (h - Module.finrank K S) S (by omega) (by omega)

lemma span_dim {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U) (k : ℕ) (hk : k ≤ h)
    (u : Fin (k + 1) → V) (hli : LinearIndependent F u) (hu : ∀ j, u j ∈ U) :
    Module.finrank K ↥(Submodule.span K (Set.range u)) = k + 1 := by
  have : Module.Finite F K := Module.Finite.of_finite
  have : Module.Finite F V := Module.Finite.trans K V
  have h1 : Module.finrank K ↥(Submodule.span K (Set.range u)) ≤ k + 1 := by
    have := finrank_range_le_card (R := K) u
    rw [Fintype.card_fin] at this
    exact this
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  set S := Submodule.span K (Set.range u) with hS
  have h2 := scat_down h U hU S (by omega)
  have hmem : ∀ j, u j ∈ S.restrictScalars F ⊓ U := fun j =>
    ⟨Submodule.subset_span ⟨j, rfl⟩, hu j⟩
  let s : Fin (k + 1) → ↥(S.restrictScalars F ⊓ U) := fun j => ⟨u j, hmem j⟩
  have hs : LinearIndependent F s :=
    LinearIndependent.of_comp (S.restrictScalars F ⊓ U).subtype hli
  have := hs.fintype_card_le_finrank
  simp at this
  omega

lemma LIcount {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]
    (E : Submodule F V) (m : ℕ) :
    ((Nat.card {s : Fin m → E // LinearIndependent F s} : ℕ) : ℤ) =
      ∏ j ∈ Finset.range m, ((Fintype.card F : ℤ) ^ Module.finrank F E - (Fintype.card F : ℤ) ^ j) := by
  by_cases hm : m ≤ Module.finrank F E
  · rw [card_linearIndependent (K := F) (V := E) hm]
    push_cast
    rw [← Fin.prod_univ_eq_prod_range (fun j => ((Fintype.card F : ℤ) ^ Module.finrank F E -
      (Fintype.card F : ℤ) ^ j)) m]
    apply Finset.prod_congr rfl
    intro j _
    have : Fintype.card F ^ (j : ℕ) ≤ Fintype.card F ^ Module.finrank F E :=
      Nat.pow_le_pow_right Fintype.card_pos (by omega)
    rw [Nat.cast_sub this]; push_cast; rfl
  · have hz : Nat.card {s : Fin m → E // LinearIndependent F s} = 0 := by
      rw [Nat.card_eq_zero]; left
      constructor
      rintro ⟨s, hs⟩
      have := hs.fintype_card_le_finrank
      simp at this
      omega
    rw [hz]
    symm
    simp only [Nat.cast_zero]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : Module.finrank F E < m))
    exact sub_self _

lemma card_LI_sub {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]
    [Fintype V] (E : Submodule F V) (m : ℕ) [DecidablePred (fun u : Fin m → V =>
      LinearIndependent F u ∧ ∀ j, u j ∈ E)] [Fintype (Fin m → V)] :
    ((Finset.univ.filter (fun u : Fin m → V => LinearIndependent F u ∧ ∀ j, u j ∈ E)).card : ℤ) =
      ∏ j ∈ Finset.range m, ((Fintype.card F : ℤ) ^ Module.finrank F E - (Fintype.card F : ℤ) ^ j) := by
  rw [← LIcount E m]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun u => ⟨fun j => ⟨u.1 j, u.2.2 j⟩,
        LinearIndependent.of_comp E.subtype (by exact u.2.1)⟩
      invFun := fun s => ⟨fun j => (s.1 j : V), by
        refine ⟨?_, fun j => (s.1 j).2⟩
        exact s.2.map' E.subtype (Submodule.ker_subtype E), ⟩
      left_inv := fun u => rfl
      right_inv := fun s => rfl }

set_option maxHeartbeats 2000000 in
theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (k : ℕ) (hk : k < h + 1) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
          ∏ j ∈ Finset.range (k + 1), ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ j) =
      (∏ j ∈ Finset.range (k + 1),
          ((Fintype.card F : ℤ) ^ Module.finrank F U - (Fintype.card F : ℤ) ^ j)) *
        ((Fintype.card F : ℤ) ^ ((Module.finrank K V - k - 1) * Module.finrank F K) - 1) := by
  classical
  have hr : 0 < Module.finrank K V := by have := hU.2.1; omega
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Module.Finite F V := Module.Finite.trans K V
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Finite (Submodule K V) :=
    Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype (Submodule K V) := Fintype.ofFinite _
  set qq : ℤ := (Fintype.card F : ℤ) with hqq
  set r := Module.finrank K V with hrdef
  set n := Module.finrank F K with hn
  set g : Submodule K V → ℕ := fun W => Module.finrank F ↥(W.restrictScalars F ⊓ U) with hg
  set Hs : Finset (Submodule K V) :=
    Finset.univ.filter (fun W => Module.finrank K W = r - 1) with hHs
  set LIU : Finset (Fin (k + 1) → V) :=
    Finset.univ.filter (fun u => LinearIndependent F u ∧ ∀ j, u j ∈ U) with hLIU
  set cW : Submodule K V → Finset (Fin (k + 1) → V) :=
    fun W => LIU.filter (fun u => ∀ j, u j ∈ W) with hcW
  -- Claim A
  have hA : ∀ W : Submodule K V, ((cW W).card : ℤ) =
      ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
    intro W
    rw [← card_LI_sub (W.restrictScalars F ⊓ U) (k + 1)]
    congr 2
    ext u
    simp only [hcW, hLIU, Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_inf,
      Submodule.restrictScalars_mem, forall_and]
    tauto
  -- Claim C
  have hC : ∑ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) =
      ∑ W ∈ Hs, ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
    have hmaps : ∀ W ∈ Hs, g W ∈ Finset.range (Module.finrank F U + 1) := by
      intro W _
      have : Module.finrank F ↥(W.restrictScalars F ⊓ U) ≤ Module.finrank F U :=
        Submodule.finrank_mono inf_le_right
      simp only [Finset.mem_range, hg]; omega
    rw [← Finset.sum_fiberwise_of_maps_to (s := Hs) (g := g)
      (t := Finset.range (Module.finrank F U + 1)) hmaps]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_congr rfl (fun W hW => by rw [(Finset.mem_filter.mp hW).2]), Finset.sum_const,
      nsmul_eq_mul]
    congr 2
    unfold HScattered.Hyperplanes.hCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp only [hHs, hg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  -- Claim B
  have hKc : Nat.card K = Fintype.card F ^ n := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := K)]
  have hB : ∀ u ∈ LIU, ((Hs.filter (fun W => ∀ j, u j ∈ W)).card : ℤ) * (qq ^ n - 1) =
      qq ^ (n * (r - (k + 1))) - 1 := by
    intro u hu
    obtain ⟨hli, huU⟩ := (Finset.mem_filter.mp hu).2
    have hspan := span_dim h U hU k (by omega) u hli huU
    set S := Submodule.span K (Set.range u) with hS
    have hle : Module.finrank K S ≤ r := Submodule.finrank_le S
    have h1 := hyp_count_ge K V S hle hr
    have hcard : Nat.card {W : Submodule K V // Module.finrank K W = r - 1 ∧ S ≤ W} =
        (Hs.filter (fun W => ∀ j, u j ∈ W)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hHs, Finset.filter_filter]
      congr 1
      ext W
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS, Submodule.span_le,
        Set.range_subset_iff]
      exact Iff.rfl
    rw [hcard, hspan, hKc, ← hrdef] at h1
    have h4 : 1 ≤ Fintype.card F ^ n := Nat.one_le_pow _ _ Fintype.card_pos
    have h5 : 1 ≤ (Fintype.card F ^ n) ^ (r - (k + 1)) := Nat.one_le_pow _ _ h4
    have h6 := congrArg (fun m : ℕ => (m : ℤ)) h1
    simp only [Nat.cast_mul, Nat.cast_sub h4, Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at h6
    rw [h6, ← pow_mul]
  -- double counting
  have hD : ∑ W ∈ Hs, (cW W).card = ∑ u ∈ LIU, (Hs.filter (fun W => ∀ j, u j ∈ W)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Hs) (t := LIU)
      (fun (W : Submodule K V) (u : Fin (k + 1) → V) => ∀ j, u j ∈ W)
  have hL : (LIU.card : ℤ) =
      ∏ j ∈ Finset.range (k + 1), (qq ^ (Module.finrank F U) - qq ^ j) := card_LI_sub U (k + 1)
  have hsum : (∑ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * (qq ^ n - 1) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j)) =
      (qq ^ n - 1) * ∑ W ∈ Hs, ((cW W).card : ℤ) := by
    calc _ = (qq ^ n - 1) * ∑ i ∈ Finset.range (Module.finrank F U + 1),
          (hCount F K U i : ℤ) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (qq ^ n - 1) * ∑ W ∈ Hs, ∏ j ∈ Finset.range (k + 1), (qq ^ (g W) - qq ^ j) := by
          rw [hC]
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl (fun W _ => (hA W).symm)
  have hfin : (qq ^ n - 1) * ∑ W ∈ Hs, ((cW W).card : ℤ) =
      (LIU.card : ℤ) * (qq ^ (n * (r - (k + 1))) - 1) := by
    rw [← Nat.cast_sum, hD, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun u hu => by rw [mul_comm, hB u hu]), Finset.sum_const,
      nsmul_eq_mul]
  have hexp : (r - k - 1) * n = n * (r - (k + 1)) := by rw [Nat.sub_sub, mul_comm]
  -- reassemble the goal
  have e1 : ∀ i ∈ Finset.range (Module.finrank F U + 1),
      (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
          ∏ j ∈ Finset.range (k + 1), ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ j) =
      (hCount F K U i : ℤ) * (qq ^ n - 1) * ∏ j ∈ Finset.range (k + 1), (qq ^ i - qq ^ j) :=
    fun i _ => rfl
  rw [Finset.sum_congr rfl e1, hsum, hfin, hL, hexp, mul_comm]
