-- Prove2me | solution 1 for GroupIsoPoly.charSeries_srad
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:21:13.098802+00:00
-- url     : https://prove2.me/submissions/883f3b50-f406-4f96-9e9a-a6d36dc24da5

import Mathlib
import Definitions.Def_cfsg_elementary_abelian
import Definitions.Def_GroupIsoPoly_charSeries

set_option autoImplicit false

namespace GroupIsoPoly.CSAux
open GroupIsoPoly

universe u v


section iso
variable {K : Type u} {K' : Type v} [Group K] [Group K']

lemma map_symm_map (ψ : K ≃* K') (N : Subgroup K) :
    (N.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = N := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id N
  ext x; simp

lemma map_eq_of_le_le (ψ : K ≃* K') (A : Subgroup K) (B : Subgroup K')
    (h1 : A.map ψ.toMonoidHom ≤ B) (h2 : B.map ψ.symm.toMonoidHom ≤ A) :
    A.map ψ.toMonoidHom = B := by
  refine le_antisymm h1 ?_
  have := Subgroup.map_mono (f := ψ.toMonoidHom) h2
  rwa [show (B.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = B from map_symm_map ψ.symm B] at this

lemma solvable_map (ψ : K ≃* K') (N : Subgroup K) [h : Group.IsSolvable N] :
    Group.IsSolvable (N.map ψ.toMonoidHom) :=
  Group.isSolvable_of_surjective (f := (N.equivMapOfInjective ψ.toMonoidHom ψ.injective).toMonoidHom)
    (MulEquiv.surjective _)

lemma srad_map_le (ψ : K ≃* K') : (srad K).map ψ.toMonoidHom ≤ srad K' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have := hN.1
  have := hN.2
  exact le_sSup ⟨hN.1.map _ ψ.surjective, solvable_map ψ N⟩

lemma srad_map (ψ : K ≃* K') : (srad K).map ψ.toMonoidHom = srad K' :=
  map_eq_of_le_le ψ _ _ (srad_map_le ψ) (srad_map_le ψ.symm)

lemma isMinimalNormal_map (ψ : K ≃* K') (N : Subgroup K) (h : IsMinimalNormal N) :
    IsMinimalNormal (N.map ψ.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.map _ ψ.surjective, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective]
  · intro M hM hM0 hle
    have e := h3 (M.map ψ.symm.toMonoidHom) (hM.map _ ψ.symm.surjective)
      (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ ψ.symm.injective])
      (by
        have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hle
        rwa [map_symm_map] at this)
    have := map_symm_map ψ.symm M
    rw [MulEquiv.symm_symm] at this
    rw [← e, this]

lemma soc_map_le (ψ : K ≃* K') : (soc K).map ψ.toMonoidHom ≤ soc K' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (isMinimalNormal_map ψ N hN)

lemma soc_map (ψ : K ≃* K') : (soc K).map ψ.toMonoidHom = soc K' :=
  map_eq_of_le_le ψ _ _ (soc_map_le ψ) (soc_map_le ψ.symm)

/-- the induced isomorphism of solvable radicals -/
noncomputable def sradEquiv (ψ : K ≃* K') : srad K ≃* srad K' :=
  ((srad K).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (srad_map ψ))

lemma derivedSeries_srad_map (ψ : K ≃* K') (n : ℕ) :
    (derivedSeries (srad K) n).map (sradEquiv ψ).toMonoidHom = derivedSeries (srad K') n :=
  map_derivedSeries_eq (sradEquiv ψ).surjective n

lemma derivedLen_eq (ψ : K ≃* K') : derivedLen K = derivedLen K' := by
  unfold derivedLen
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  rw [← derivedSeries_srad_map ψ, Subgroup.map_eq_bot_iff_of_injective _ (sradEquiv ψ).injective]

lemma lastDerived_map (ψ : K ≃* K') :
    (lastDerived K).map ψ.toMonoidHom = lastDerived K' := by
  unfold lastDerived
  rw [← derivedLen_eq ψ, ← derivedSeries_srad_map ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

lemma acPrime_eq (ψ : K ≃* K') : acPrime K = acPrime K' := by
  unfold acPrime
  rw [← lastDerived_map ψ, Subgroup.card_map_of_injective ψ.injective]

lemma AC_map (ψ : K ≃* K') : (AC K).map ψ.toMonoidHom = AC K' := by
  unfold AC
  rw [Subgroup.map_normalClosure _ _ ψ.surjective, ← acPrime_eq ψ, ← lastDerived_map ψ]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by simp [← map_pow, hx2]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hx2⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply ψ.injective
    rw [map_pow, map_one]
    simpa using hx2

lemma srad_eq_bot_iff (ψ : K ≃* K') : srad K = ⊥ ↔ srad K' = ⊥ := by
  rw [← srad_map ψ, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective]

lemma S_map (ψ : K ≃* K') : (S K).map ψ.toMonoidHom = S K' := by
  unfold S
  by_cases h : srad K = ⊥
  · rw [if_pos h, if_pos ((srad_eq_bot_iff ψ).mp h), soc_map]
  · rw [if_neg h, if_neg (mt (srad_eq_bot_iff ψ).mpr h), AC_map]

end iso

lemma charSeries_succ (Q : Type u) [Group Q] (i : ℕ) :
    charSeries Q (i + 1) = (S (Q ⧸ charSeries Q i)).comap (QuotientGroup.mk' (charSeries Q i)) :=
  rfl

lemma charSeries_zero (Q : Type u) [Group Q] : charSeries Q 0 = ⊥ := rfl

lemma charSeries_map {Q : Type u} {Q' : Type v} [Group Q] [Group Q'] (φ : Q ≃* Q') (i : ℕ) :
    (charSeries Q i).map φ.toMonoidHom = charSeries Q' i := by
  induction i with
  | zero => rw [charSeries_zero, charSeries_zero, Subgroup.map_bot]
  | succ i ih =>
    rw [charSeries_succ, charSeries_succ]
    set φb := QuotientGroup.congr (charSeries Q i) (charSeries Q' i) φ ih
    rw [← S_map φb]
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, hy, QuotientGroup.congr_mk _ _ _ _ _⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨φ.symm x, ?_, by simp⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
      have : (y : Q ⧸ charSeries Q i) = ((φ.symm x : Q) : Q ⧸ charSeries Q i) := by
        apply φb.injective
        have h2 : φb.toMonoidHom (y : Q ⧸ charSeries Q i) = φb (y : Q ⧸ charSeries Q i) := rfl
        rw [← h2, hzx]
        have h3 := QuotientGroup.congr_mk (charSeries Q i) (charSeries Q' i) φ ih (φ.symm x)
        rw [MulEquiv.apply_symm_apply] at h3
        exact h3.symm
      rwa [← this]



section fin
variable {K : Type u} [Group K]

lemma extension_solvable {P : Type u} [Group P] (N : Subgroup P) [N.Normal]
    [Group.IsSolvable N] [Group.IsSolvable (P ⧸ N)] : Group.IsSolvable P :=
  Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

lemma sup_solvable (N M : Subgroup K) [N.Normal] [M.Normal] [Group.IsSolvable N]
    [Group.IsSolvable M] : Group.IsSolvable ↥(N ⊔ M) := by
  let N' := N.subgroupOf (N ⊔ M)
  have : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ M)).toMonoidHom)
      (MulEquiv.injective _)
  have : Group.IsSolvable (↥(N ⊔ M) ⧸ N') := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' N').comp (Subgroup.inclusion (le_sup_right : M ≤ N ⊔ M))) ?_
    intro q
    obtain ⟨⟨p, hp⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hp
    refine ⟨⟨m, hm⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simp only [N', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inclusion]
    have : (m : K)⁻¹ * (n * m) = m⁻¹ * n * m⁻¹⁻¹ := by group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance n hn m⁻¹
  exact extension_solvable N'

lemma le_srad (N : Subgroup K) [hN : N.Normal] [hs : Group.IsSolvable N] : N ≤ srad K :=
  le_sSup ⟨hN, hs⟩

lemma srad_solvable [Finite K] : Group.IsSolvable (srad K) := by
  let 𝒮 : Set (Subgroup K) := {N | N.Normal ∧ Group.IsSolvable N}
  obtain ⟨N0, hN0⟩ := (Set.toFinite 𝒮).exists_maximal
    ⟨⊥, ⟨inferInstance, inferInstance⟩⟩
  have key : srad K = N0 := by
    refine le_antisymm (sSup_le fun N hN => ?_) (le_sSup hN0.1)
    have := hN.1; have := hN.2; have := hN0.1.1; have := hN0.1.2
    have h1 : N ⊔ N0 ∈ 𝒮 := ⟨inferInstance, sup_solvable N N0⟩
    exact le_sup_left.trans (hN0.2 h1 le_sup_right)
  rw [key]; exact hN0.1.2

lemma srad_eq_top [Group.IsSolvable K] : srad K = ⊤ := by
  have : Group.IsSolvable (⊤ : Subgroup K) :=
    Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup K).subtype) Subtype.val_injective
  exact le_antisymm le_top (le_srad ⊤)

lemma derivedLen_spec [Finite K] : derivedSeries (srad K) (derivedLen K + 1) = ⊥ := by
  have := srad_solvable (K := K)
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := srad K)
  apply Nat.sInf_mem (s := {n : ℕ | derivedSeries (srad K) (n + 1) = ⊥})
  exact ⟨n, le_bot_iff.mp ((derivedSeries_antitone (srad K) (Nat.le_succ n)).trans hn.le)⟩

lemma derivedLen_ne [Finite K] (h : srad K ≠ ⊥) : derivedSeries (srad K) (derivedLen K) ≠ ⊥ := by
  intro h0
  cases hd : derivedLen K with
  | zero =>
    rw [hd, derivedSeries_zero] at h0
    apply h
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : srad K) ∈ (⊥ : Subgroup (srad K)) := h0 ▸ Subgroup.mem_top _
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  | succ n =>
    have : n < derivedLen K := by omega
    exact Nat.notMem_of_lt_sInf this (by rw [hd] at h0; exact h0)

lemma lastDerived_ne_bot [Finite K] (h : srad K ≠ ⊥) : lastDerived K ≠ ⊥ := by
  unfold lastDerived
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (srad K).subtype_injective]
  exact derivedLen_ne h

lemma lastDerived_comm [Finite K] {x y : K} (hx : x ∈ lastDerived K) (hy : y ∈ lastDerived K) :
    x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hc := Subgroup.commutator_mem_commutator ha hb
  rw [← derivedSeries_succ, derivedLen_spec, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at hc
  simp only [Subgroup.coe_subtype]
  rw [← Subgroup.coe_mul, hc, Subgroup.coe_mul]

instance lastDerived_normal : (lastDerived K).Normal := by
  unfold lastDerived
  infer_instance

/-- the subgroup `{y ∈ D : y ^ r = 1}` -/
def Ysub [Finite K] : Subgroup K where
  carrier := {y | y ∈ lastDerived K ∧ y ^ acPrime K = 1}
  mul_mem' {a b} ha hb := ⟨(lastDerived K).mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (lastDerived_comm ha.1 hb.1)), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨(lastDerived K).one_mem, one_pow _⟩
  inv_mem' {a} ha := ⟨(lastDerived K).inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

instance Ysub_normal [Finite K] : (Ysub (K := K)).Normal :=
  ⟨fun y hy g => ⟨(lastDerived_normal).conj_mem y hy.1 g, by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩

lemma AC_le_Ysub [Finite K] : AC K ≤ Ysub := by
  unfold AC
  exact Subgroup.normalClosure_le_normal fun y hy => hy

lemma acPrime_prime [Finite K] (h : srad K ≠ ⊥) : (acPrime K).Prime := by
  unfold acPrime
  apply Nat.minFac_prime
  intro h1
  exact lastDerived_ne_bot h (Subgroup.card_eq_one.mp h1)

lemma AC_ne_bot [Finite K] (h : srad K ≠ ⊥) : AC K ≠ ⊥ := by
  have hp := acPrime_prime h
  haveI : Fact (acPrime K).Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := lastDerived K) (acPrime K)
    (Nat.minFac_dvd _)
  intro h0
  have hmem : (x : K) ∈ AC K := Subgroup.subset_normalClosure
    ⟨x.2, by rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]⟩
  rw [h0, Subgroup.mem_bot] at hmem
  have : x = 1 := Subtype.ext hmem
  rw [this, orderOf_one] at hx
  exact hp.one_lt.ne hx

lemma AC_elem [Finite K] (h : srad K ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ IsElementaryAbelian r (AC K) := by
  refine ⟨acPrime K, acPrime_prime h, ?_⟩
  exact
    { is_comm := ⟨fun a b => Subtype.ext (lastDerived_comm (AC_le_Ysub a.2).1 (AC_le_Ysub b.2).1)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by rw [Subgroup.coe_pow, (AC_le_Ysub a.2).2, Subgroup.coe_one]) }

lemma exists_minimalNormal [Finite K] [Nontrivial K] : ∃ N : Subgroup K, IsMinimalNormal N := by
  let 𝒩 : Set (Subgroup K) := {N | N.Normal ∧ N ≠ ⊥}
  obtain ⟨N, hN⟩ := (Set.toFinite 𝒩).exists_minimal ⟨⊤, inferInstance, top_ne_bot⟩
  exact ⟨N, hN.1.1, hN.1.2, fun M hM hM0 hle => le_antisymm hle (hN.2 ⟨hM, hM0⟩ hle)⟩

lemma soc_ne_bot [Finite K] [Nontrivial K] : soc K ≠ ⊥ := by
  obtain ⟨N, hN⟩ := exists_minimalNormal (K := K)
  intro h
  exact hN.2.1 (le_bot_iff.mp (h ▸ le_sSup hN))

lemma S_ne_bot [Finite K] [Nontrivial K] : S K ≠ ⊥ := by
  unfold S
  split_ifs with h
  · exact soc_ne_bot
  · exact AC_ne_bot h

lemma AC_le_srad [Finite K] : AC K ≤ srad K := by
  intro x hx
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := AC_le_Ysub hx
  exact y.2

end fin


section prod

lemma isProd_iso {G G' : Type u} [Group G] [Group G'] (h : IsProdNonabelianSimple G)
    (e : G ≃* G') : IsProdNonabelianSimple G' := by
  obtain ⟨k, T, iT, hT, ⟨f⟩⟩ := h
  exact ⟨k, T, iT, hT, ⟨e.symm.trans f⟩⟩

lemma isProd_subsingleton {G : Type u} [Group G] [Subsingleton G] : IsProdNonabelianSimple G :=
  ⟨0, fun _ => PUnit, fun _ => inferInstance, fun i => i.elim0,
    ⟨{ toFun := fun _ => 1, invFun := fun _ => 1,
       left_inv := fun _ => Subsingleton.elim _ _, right_inv := fun _ => Subsingleton.elim _ _,
       map_mul' := fun _ _ => (mul_one 1).symm }⟩⟩

lemma isProd_simple {G : Type u} [Group G] [IsSimpleGroup G] (h : ∃ x y : G, x * y ≠ y * x) :
    IsProdNonabelianSimple G :=
  ⟨1, fun _ => G, fun _ => inferInstance, fun _ => ⟨inferInstance, h⟩,
    ⟨(MulEquiv.piUnique (fun _ : Fin 1 => G)).symm⟩⟩

lemma isProd_prod {A B : Type u} [Group A] [Group B] (hA : IsProdNonabelianSimple A)
    (hB : IsProdNonabelianSimple B) : IsProdNonabelianSimple (A × B) := by
  obtain ⟨k, T, iT, hT, ⟨eA⟩⟩ := hA
  obtain ⟨k', T', iT', hT', ⟨eB⟩⟩ := hB
  let V : Fin k ⊕ Fin k' → Type u := Sum.elim T T'
  letI iV : ∀ s, Group (V s) := fun s => match s with
    | .inl i => iT i
    | .inr j => iT' j
  have hV : ∀ s, IsSimpleGroup (V s) ∧ ∃ x y : V s, x * y ≠ y * x := by
    intro s
    cases s with
    | inl i => exact hT i
    | inr j => exact hT' j
  let e := finSumFinEquiv (m := k) (n := k')
  let P : ((i : Fin k) → T i) × ((j : Fin k') → T' j) ≃* ((s : Fin k ⊕ Fin k') → V s) :=
    { toFun := fun p s => match s with
        | .inl i => p.1 i
        | .inr j => p.2 j
      invFun := fun f => (fun i => f (.inl i), fun j => f (.inr j))
      left_inv := fun p => rfl
      right_inv := fun f => funext fun s => by cases s <;> rfl
      map_mul' := fun p q => funext fun s => by cases s <;> rfl }
  let R : ((s : Fin k ⊕ Fin k') → V s) ≃* ((x : Fin (k + k')) → V (e.symm x)) :=
    { Equiv.piCongrLeft' V e with map_mul' := fun f g => rfl }
  refine ⟨k + k', fun x => V (e.symm x), fun x => iV (e.symm x), ?_,
    ⟨((MulEquiv.prodCongr eA eB).trans P).trans R⟩⟩
  intro x
  exact hV (e.symm x)

/-- two normal subgroups meeting trivially generate their direct product -/
noncomputable def supEquiv {H : Type u} [Group H] (A B : Subgroup H) [hA : A.Normal] [hB : B.Normal]
    (hd : A ⊓ B = ⊥) : ↥(A ⊔ B) ≃* ↥A × ↥B := by
  have comm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    Subgroup.commute_of_normal_of_disjoint A B hA hB (disjoint_iff.mpr hd) a b a.2 b.2
  let φ := MonoidHom.noncommCoprod A.subtype B.subtype comm
  have inj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : H) * b = 1 := hab
    have ha : (a : H) ∈ A ⊓ B := ⟨a.2, by
      rw [eq_inv_of_mul_eq_one_left h1]; exact B.inv_mem b.2⟩
    rw [hd, Subgroup.mem_bot] at ha
    have hb : (b : H) = 1 := by rw [ha, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hr : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ((MonoidHom.ofInjective inj).trans (MulEquiv.subgroupCongr hr)).symm

lemma greedy {H : Type u} [Group H] [Finite H] (𝒳 : Set (Subgroup H))
    (h1 : ∀ X ∈ 𝒳, X.Normal) (h2 : ∀ X ∈ 𝒳, ∀ N : Subgroup H, N.Normal → X ≤ N ∨ X ⊓ N = ⊥)
    (h3 : ∀ X ∈ 𝒳, IsProdNonabelianSimple X) : IsProdNonabelianSimple ↥(sSup 𝒳) := by
  let PP : Set (Subgroup H) := {P | P.Normal ∧ P ≤ sSup 𝒳 ∧ IsProdNonabelianSimple P}
  obtain ⟨P, hP⟩ := (Set.toFinite PP).exists_maximal
    ⟨⊥, inferInstance, bot_le, isProd_subsingleton⟩
  have key : P = sSup 𝒳 := by
    refine le_antisymm hP.1.2.1 (sSup_le fun X hX => ?_)
    by_contra hXP
    have := hP.1.1
    have := h1 X hX
    have hd : X ⊓ P = ⊥ := (h2 X hX P hP.1.1).resolve_left hXP
    have hmem : P ⊔ X ∈ PP := ⟨inferInstance, sup_le hP.1.2.1 (le_sSup hX),
      isProd_iso (isProd_prod hP.1.2.2 (h3 X hX)) (supEquiv P X (by rw [inf_comm, hd])).symm⟩
    exact hXP (le_sup_right.trans (hP.2 hmem le_sup_left))
  rw [← key]
  exact hP.1.2.2

end prod

section socle

lemma minNormal_atomic {G : Type u} [Group G] (X N : Subgroup G) (hX : IsMinimalNormal X)
    (hN : N.Normal) : X ≤ N ∨ X ⊓ N = ⊥ := by
  by_cases h : X ⊓ N = ⊥
  · exact Or.inr h
  · left
    have := hX.1
    have e := hX.2.2 (X ⊓ N) inferInstance h inf_le_left
    rw [← e]
    exact inf_le_right

lemma mem_normalizer_of_conj {G : Type u} [Group G] (N : Subgroup G) (g : G)
    (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h2 : ∀ n ∈ N, g⁻¹ * n * g⁻¹⁻¹ ∈ N) :
    g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun h => ?_⟩
  have := h2 _ h
  simpa [mul_assoc] using this

lemma solvable_map_subtype {G : Type u} [Group G] (M : Subgroup G) (L : Subgroup M)
    [Group.IsSolvable L] : Group.IsSolvable (L.map M.subtype) :=
  Group.isSolvable_of_surjective (f := (L.equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
    (MulEquiv.surjective _)

lemma map_subtype_top {G : Type u} [Group G] (M : Subgroup G) :
    (⊤ : Subgroup M).map M.subtype = M := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

lemma minNormal_isProd {K : Type u} [Group K] [Finite K] (hK : srad K = ⊥) (M : Subgroup K)
    (hM : IsMinimalNormal M) : IsProdNonabelianSimple M := by
  have := hM.1
  have charSoc : (soc M).Characteristic :=
    Subgroup.characteristic_iff_map_eq.mpr fun ϕ => soc_map ϕ
  have charSrad : (srad M).Characteristic :=
    Subgroup.characteristic_iff_map_eq.mpr fun ϕ => srad_map ϕ
  have hsr : srad M = ⊥ := by
    have := srad_solvable (K := M)
    have := solvable_map_subtype M (srad M)
    have h := le_srad ((srad M).map M.subtype)
    rwa [hK, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective] at h
  have hsoc : soc M = ⊤ := by
    haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM.2.1
    have hne : (soc M).map M.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
      exact soc_ne_bot
    have hle : (soc M).map M.subtype ≤ M := Subgroup.map_subtype_le _
    have e := hM.2.2 _ inferInstance hne hle
    exact Subgroup.map_injective M.subtype_injective (e.trans (map_subtype_top M).symm)
  have hX : ∀ X : Subgroup M, IsMinimalNormal X → IsProdNonabelianSimple X := by
    intro X hX
    have := hX.1
    haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX.2.1
    haveI : IsSimpleGroup X := by
      refine ⟨fun N hN => ?_⟩
      let N' := N.map X.subtype
      have hN'X : N' ≤ X := Subgroup.map_subtype_le _
      have hN' : N'.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsoc]
        refine sSup_le fun Y hY => ?_
        intro y hy
        by_cases hYX : Y = X
        · subst hYX
          have C : ∀ z ∈ Y, ∀ n ∈ N', z * n * z⁻¹ ∈ N' := by
            intro z hz n hn
            obtain ⟨n0, hn0, rfl⟩ := hn
            refine ⟨⟨z, hz⟩ * n0 * ⟨z, hz⟩⁻¹, hN.conj_mem n0 hn0 ⟨z, hz⟩, ?_⟩
            simp
          exact mem_normalizer_of_conj N' y (C y hy) (C y⁻¹ (Y.inv_mem hy))
        · have hd : X ⊓ Y = ⊥ := by
            rcases minNormal_atomic X Y hX hY.1 with h | h
            · exact absurd (hY.2.2 X hX.1 hX.2.1 h).symm hYX
            · exact h
          have := hY.1
          have C : ∀ z ∈ Y, ∀ n ∈ N', z * n * z⁻¹ ∈ N' := by
            intro z hz n hn
            have hc := Subgroup.commute_of_normal_of_disjoint X Y inferInstance inferInstance
              (disjoint_iff.mpr hd) n z (hN'X hn) hz
            rw [← hc.eq, mul_inv_cancel_right]
            exact hn
          exact mem_normalizer_of_conj N' y (C y hy) (C y⁻¹ (Y.inv_mem hy))
      by_cases h0 : N' = ⊥
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h0
      · right
        have e := hX.2.2 N' hN' h0 hN'X
        exact Subgroup.map_injective X.subtype_injective (e.trans (map_subtype_top X).symm)
    apply isProd_simple
    by_contra hc
    push_neg at hc
    have : Group.IsSolvable X := isSolvable_of_comm hc
    have h := le_srad X
    rw [hsr] at h
    exact hX.2.1 (le_bot_iff.mp h)
  have h := greedy {X : Subgroup M | IsMinimalNormal X} (fun X h => h.1)
    (fun X h N hN => minNormal_atomic X N h hN) hX
  have e : sSup {X : Subgroup M | IsMinimalNormal X} = soc M := rfl
  rw [e, hsoc] at h
  exact isProd_iso h Subgroup.topEquiv

lemma soc_isProd {K : Type u} [Group K] [Finite K] (hK : srad K = ⊥) :
    IsProdNonabelianSimple (soc K) :=
  greedy {X : Subgroup K | IsMinimalNormal X} (fun X h => h.1)
    (fun X h N hN => minNormal_atomic X N h hN) (fun X h => minNormal_isProd hK X h)

end socle

section series

lemma charSeries_mono (Q : Type u) [Group Q] (i : ℕ) : charSeries Q i ≤ charSeries Q (i + 1) := by
  intro x hx
  rw [charSeries_succ, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

lemma charSeries_lt (Q : Type u) [Group Q] [Finite Q] (i : ℕ) (h : charSeries Q i ≠ ⊤) :
    charSeries Q i < charSeries Q (i + 1) := by
  refine lt_of_le_of_ne (charSeries_mono Q i) fun e => ?_
  haveI : Nontrivial (Q ⧸ charSeries Q i) := QuotientGroup.nontrivial_iff.mpr h
  apply S_ne_bot (K := Q ⧸ charSeries Q i)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ charSeries Q (i + 1) := hy
  rw [← e] at hx
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)

lemma card_double (Q : Type u) [Group Q] [Finite Q] (i : ℕ) (h : charSeries Q i ≠ ⊤) :
    2 * Nat.card (charSeries Q i) ≤ Nat.card (charSeries Q (i + 1)) := by
  have hlt := charSeries_lt Q i h
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hlt.le
  have hpos : 0 < Nat.card (charSeries Q i) := Nat.card_pos
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hc.le)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact (Nat.card_pos (α := charSeries Q (i + 1))).ne' hc
  rw [hc]
  have : 2 ≤ c := by omega
  nlinarith

lemma pow_le_card (Q : Type u) [Group Q] [Finite Q] (i : ℕ) (h : ∀ j < i, charSeries Q j ≠ ⊤) :
    2 ^ i ≤ Nat.card (charSeries Q i) := by
  induction i with
  | zero => exact Nat.card_pos
  | succ i ih =>
    have := card_double Q i (h i (Nat.lt_succ_self i))
    have := ih fun j hj => h j (by omega)
    rw [pow_succ]
    omega

lemma exists_top (Q : Type u) [Group Q] [Finite Q] : ∃ i, charSeries Q i = ⊤ := by
  by_contra hne
  push Not at hne
  have h1 := pow_le_card Q (Nat.card Q) (fun j _ => hne j)
  have h2 := Subgroup.card_le_card_group (charSeries Q (Nat.card Q))
  have h3 := Nat.lt_two_pow_self (n := Nat.card Q)
  omega

lemma seriesLength_spec (Q : Type u) [Group Q] [Finite Q] :
    charSeries Q (seriesLength Q) = ⊤ :=
  Nat.sInf_mem (s := {i : ℕ | charSeries Q i = ⊤}) (exists_top Q)

lemma lt_seriesLength (Q : Type u) [Group Q] (j : ℕ) (hj : j < seriesLength Q) :
    charSeries Q j ≠ ⊤ :=
  Nat.notMem_of_lt_sInf hj

lemma seriesLength_le_log (Q : Type u) [Group Q] [Finite Q] :
    seriesLength Q ≤ Nat.log 2 (Nat.card Q) := by
  apply Nat.le_log_of_pow_le one_lt_two
  have := pow_le_card Q (seriesLength Q) (fun j hj => lt_seriesLength Q j hj)
  rwa [seriesLength_spec, Subgroup.card_top] at this

lemma srad_quot (Q : Type u) [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (hN : N ≤ srad Q) : srad (Q ⧸ N) = (srad Q).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · let R' := srad (Q ⧸ N)
    let P := R'.comap (QuotientGroup.mk' N)
    have hNP : N ≤ P := by
      intro x hx
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have : Group.IsSolvable (srad Q) := srad_solvable
    have : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hN)
        (Subgroup.inclusion_injective hN)
    have : Group.IsSolvable R' := srad_solvable
    have : Group.IsSolvable P := by
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNP)
        ((QuotientGroup.mk' N).subgroupComap R') ?_
      intro p hp
      rw [MonoidHom.mem_ker] at hp
      have hp' : ((p : Q) : Q ⧸ N) = 1 := congrArg Subtype.val hp
      exact ⟨⟨p, (QuotientGroup.eq_one_iff _).mp hp'⟩, rfl⟩
    have : P.Normal := Subgroup.Normal.comap inferInstance _
    have hP := le_srad P
    calc R' = P.map (QuotientGroup.mk' N) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _).symm
      _ ≤ (srad Q).map (QuotientGroup.mk' N) := Subgroup.map_mono hP
  · have : Group.IsSolvable (srad Q) := srad_solvable
    have : Group.IsSolvable ((srad Q).map (QuotientGroup.mk' N)) :=
      Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).subgroupMap (srad Q))
        (MonoidHom.subgroupMap_surjective _ _)
    have : ((srad Q).map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    exact le_srad _

lemma srad_quot_ne (Q : Type u) [Group Q] [Finite Q] (i : ℕ) (h1 : charSeries Q i ≤ srad Q)
    (h2 : ¬ srad Q ≤ charSeries Q i) : srad (Q ⧸ charSeries Q i) ≠ ⊥ := by
  rw [srad_quot Q _ h1]
  intro h0
  apply h2
  intro x hx
  have : (x : Q ⧸ charSeries Q i) ∈ (srad Q).map (QuotientGroup.mk' (charSeries Q i)) :=
    ⟨x, hx, rfl⟩
  rw [h0, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).mp this

lemma srad_step (Q : Type u) [Group Q] [Finite Q] (i : ℕ) (h1 : charSeries Q i ≤ srad Q)
    (h2 : ¬ srad Q ≤ charSeries Q i) : charSeries Q (i + 1) ≤ srad Q := by
  have hq := srad_quot Q (charSeries Q i) h1
  have hne := srad_quot_ne Q i h1 h2
  rw [charSeries_succ]
  unfold S
  rw [if_neg hne]
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have h3 := AC_le_srad hx
  rw [hq] at h3
  obtain ⟨y, hy, hxy⟩ := h3
  have h4 : y⁻¹ * x ∈ charSeries Q i := QuotientGroup.eq.mp hxy
  have := (srad Q).mul_mem hy (h1 h4)
  simpa using this

lemma quot_elem {Q : Type u} [Group Q] (N : Subgroup Q) [N.Normal] (P : Subgroup Q) (A : Subgroup (Q ⧸ N))
    (hPA : ∀ x ∈ P, (x : Q ⧸ N) ∈ A) (r : ℕ) (hA : IsElementaryAbelian r A) :
    IsElementaryAbelian r (↥P ⧸ N.subgroupOf P) := by
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => (hA.is_comm).comm a b
  have hexp : ∀ a : A, a ^ r = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p
  refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
  · induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e := congrArg Subtype.val (hcomm ⟨_, hPA a a.2⟩ ⟨_, hPA b b.2⟩)
    simp only [Subgroup.coe_mul] at e
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at e
    simpa using e
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro a
    induction a using QuotientGroup.induction_on with | H a => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have e := congrArg Subtype.val (hexp ⟨_, hPA a a.2⟩)
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at e
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at e
    simpa using e

end series

end GroupIsoPoly.CSAux

open GroupIsoPoly GroupIsoPoly.CSAux

theorem solution (Q : Type*) [Group Q] [Finite Q] :
    ∃ j ≤ seriesLength Q, charSeries Q j = srad Q ∧
      (∀ i < j, ∃ r : ℕ, r.Prime ∧
        IsElementaryAbelian r
          (↥(charSeries Q (i + 1)) ⧸ (charSeries Q i).subgroupOf (charSeries Q (i + 1)))) ∧
      (∀ i < j, srad (Q ⧸ charSeries Q i) = (srad Q).map (QuotientGroup.mk' (charSeries Q i))) ∧
      (srad Q = ⊥ → j = 0) ∧
      (Group.IsSolvable Q → j = seriesLength Q) ∧
      (j < seriesLength Q →
        (charSeries Q (j + 1)).map (QuotientGroup.mk' (charSeries Q j)) = soc (Q ⧸ charSeries Q j) ∧
          IsProdNonabelianSimple (soc (Q ⧸ charSeries Q j))) := by
  have hne : {i | srad Q ≤ charSeries Q i}.Nonempty :=
    ⟨seriesLength Q, by rw [Set.mem_ofPred_eq, seriesLength_spec]; exact le_top⟩
  set j := sInf {i | srad Q ≤ charSeries Q i} with hjdef
  have hjmem : srad Q ≤ charSeries Q j := Nat.sInf_mem hne
  have hlt : ∀ i < j, ¬ srad Q ≤ charSeries Q i := fun i hi => Nat.notMem_of_lt_sInf hi
  have hle : ∀ i ≤ j, charSeries Q i ≤ srad Q := by
    intro i
    induction i with
    | zero => intro _; rw [charSeries_zero]; exact bot_le
    | succ i ih =>
      intro hi
      exact srad_step Q i (ih (by omega)) (hlt i (by omega))
  have hj : charSeries Q j = srad Q := le_antisymm (hle j le_rfl) hjmem
  have hjl : j ≤ seriesLength Q :=
    Nat.sInf_le (show srad Q ≤ charSeries Q (seriesLength Q) by rw [seriesLength_spec]; exact le_top)
  refine ⟨j, hjl, hj, fun i hi => ?_, fun i hi => srad_quot Q _ (hle i hi.le), fun h => ?_,
    fun h => ?_, fun _ => ?_⟩
  · have hn := srad_quot_ne Q i (hle i hi.le) (hlt i hi)
    obtain ⟨r, hr, hA⟩ := AC_elem hn
    refine ⟨r, hr, quot_elem (charSeries Q i) (charSeries Q (i + 1)) (AC (Q ⧸ charSeries Q i))
      (fun x hx => ?_) r hA⟩
    have hx' : x ∈ (S (Q ⧸ charSeries Q i)).comap (QuotientGroup.mk' (charSeries Q i)) := hx
    unfold S at hx'
    rw [if_neg hn] at hx'
    exact hx'
  · exact Nat.eq_zero_of_le_zero (Nat.sInf_le (show srad Q ≤ charSeries Q 0 by rw [h]; exact bot_le))
  · exact le_antisymm hjl (Nat.sInf_le (show charSeries Q j = ⊤ from hj.trans srad_eq_top))
  · have hb : srad (Q ⧸ charSeries Q j) = ⊥ := by
      rw [srad_quot Q _ (hle j le_rfl), eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hj] at hx
      exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff x).mpr hx)
    refine ⟨?_, soc_isProd hb⟩
    rw [charSeries_succ]
    unfold S
    rw [if_pos hb]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
