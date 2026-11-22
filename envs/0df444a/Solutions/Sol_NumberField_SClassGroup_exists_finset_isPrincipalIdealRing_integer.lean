-- Prove2me | solution 1 for NumberField.SClassGroup.exists_finset_isPrincipalIdealRing_integer
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:26:23.090194+00:00
-- url     : https://prove2.me/submissions/3f9da8e0-5598-40cf-a3d6-318fffef2118

import Mathlib

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_NumberField_SClassGroup_exists_finset_isPrincipalIdealRing_integer

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An element of `R` lying in no prime outside `T` is invertible in the ring of `T`-integers. -/
theorem inv_mem_integer (T : Set (HeightOneSpectrum R)) {a : R}
    (ha : ∀ v ∉ T, a ∉ v.asIdeal) : (algebraMap R K a)⁻¹ ∈ T.integer K := by
  intro v hv
  have h1 : v.valuation K (algebraMap R K a) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := K)).mpr (ha v hv)
  change v.valuation K (algebraMap R K a)⁻¹ ≤ 1
  rw [map_inv₀, h1, inv_one]

/-- If the class group of `R` is finite, every `T`-integer (`T` finite) has a denominator
that is supported in `T`: the ring of `T`-integers is a localization of `R`. -/
theorem exists_mul_eq_algebraMap [Finite (ClassGroup R)] (T : Finset (HeightOneSpectrum R))
    {x : K} (hx : x ∈ (T : Set (HeightOneSpectrum R)).integer K) :
    ∃ s : R, s ≠ 0 ∧ (∀ v ∉ (T : Set (HeightOneSpectrum R)), s ∉ v.asIdeal) ∧
      ∃ r : R, algebraMap R K s * x = algebraMap R K r := by
  classical
  let _ := Fintype.ofFinite (ClassGroup R)
  -- the product of the primes in `T`, and a generator `π` of its `h`-th power
  set P : Ideal R := ∏ v ∈ T, v.asIdeal with hP
  have hP0 : P ≠ ⊥ := by
    rw [hP, ← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => v.ne_bot
  have hPmem : P ∈ (Ideal R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hP0
  set h : ℕ := Fintype.card (ClassGroup R) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprinc : (P ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 ((⟨P, hPmem⟩ : (Ideal R)⁰) ^ h) = 1 := by
      rw [map_pow, hh, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hPmem h)).mp h1
  obtain ⟨π, hπ⟩ := hprinc
  have hπ' : P ^ h = Ideal.span {π} := hπ
  have hπmemP : π ∈ P ^ h := by rw [hπ']; exact Ideal.mem_span_singleton_self π
  -- `π` lies in every prime of `T` ...
  have hπ_mem : ∀ v ∈ T, π ∈ v.asIdeal := by
    intro v hv
    have h1 : P ≤ v.asIdeal := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    exact h1 (Ideal.pow_le_self hpos.ne' hπmemP)
  -- ... and in no prime outside `T`
  have hπ_notMem : ∀ w ∉ (T : Set (HeightOneSpectrum R)), π ∉ w.asIdeal := by
    intro w hw hmem
    have h1 : P ^ h ≤ w.asIdeal := by
      rw [hπ']; exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    have h2 : P ≤ w.asIdeal := w.isPrime.le_of_pow_le h1
    obtain ⟨v, hvT, hvw⟩ := (Ideal.IsPrime.prod_le w.isPrime).mp h2
    have h3 : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top hvw
    exact hw (by rw [← HeightOneSpectrum.ext h3]; exact hvT)
  -- a common exponent `N` clearing the denominators at the primes of `T`
  have hlt : ∀ v ∈ T, v.valuation K (algebraMap R K π) < 1 := fun v hv =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem v π).mpr (hπ_mem v hv)
  have hπ0 : π ≠ 0 := by
    intro h0
    apply hP0
    have : P ^ h = ⊥ := by rw [hπ', h0]; simp
    exact pow_eq_zero_iff hpos.ne' |>.mp this
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ0
  have harch : ∀ v : HeightOneSpectrum R, ∃ n : ℕ, v ∈ T →
      v.valuation K x ≤ ((v.valuation K (algebraMap R K π))⁻¹) ^ n := by
    intro v
    by_cases hv : v ∈ T
    · have h0 : v.valuation K (algebraMap R K π) ≠ 0 := (Valuation.ne_zero_iff _).mpr hπK
      have h1 : 1 < (v.valuation K (algebraMap R K π))⁻¹ :=
        (one_lt_inv₀ (zero_lt_iff.mpr h0)).mpr (hlt v hv)
      obtain ⟨n, hn⟩ := MulArchimedean.arch (v.valuation K x) h1
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose n hn using harch
  set N : ℕ := ∑ v ∈ T, n v with hN
  refine ⟨π ^ N, pow_ne_zero N hπ0, fun w hw hmem => hπ_notMem w hw (w.isPrime.mem_of_pow_mem N hmem),
    ?_⟩
  have hall : ∀ v : HeightOneSpectrum R, v.valuation K (algebraMap R K (π ^ N) * x) ≤ 1 := by
    intro v
    rw [map_mul]
    by_cases hv : v ∈ T
    · have h0 : v.valuation K (algebraMap R K π) ≠ 0 := (Valuation.ne_zero_iff _).mpr hπK
      have hle1 : 1 ≤ (v.valuation K (algebraMap R K π))⁻¹ :=
        (one_le_inv₀ (zero_lt_iff.mpr h0)).mpr (hlt v hv).le
      have hnN : n v ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
      have h2 : v.valuation K x ≤ ((v.valuation K (algebraMap R K π))⁻¹) ^ N :=
        (hn v hv).trans (pow_le_pow_right₀ hle1 hnN)
      calc v.valuation K (algebraMap R K (π ^ N)) * v.valuation K x
          ≤ v.valuation K (algebraMap R K (π ^ N)) *
              ((v.valuation K (algebraMap R K π))⁻¹) ^ N := by gcongr
        _ = 1 := by
            rw [map_pow, map_pow, ← mul_pow, mul_inv_cancel₀ h0, one_pow]
    · exact mul_le_one' (HeightOneSpectrum.valuation_le_one v _) (hx v hv)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hall
  exact ⟨r, hr.symm⟩

/-- **Class number one after enlarging `S`.** For a Dedekind domain with finite class group, every
finite set `S` of primes is contained in a finite set `T` whose ring of `T`-integers is a principal
ideal ring. -/
theorem exists_finset_isPrincipalIdealRing [Finite (ClassGroup R)]
    (S : Finset (HeightOneSpectrum R)) :
    ∃ T : Finset (HeightOneSpectrum R), S ⊆ T ∧
      IsPrincipalIdealRing ((T : Set (HeightOneSpectrum R)).integer K) := by
  classical
  let _ := Fintype.ofFinite (ClassGroup R)
  -- integral representatives `I c` of the ideal classes and nonzero elements `a c ∈ I c`
  choose I hI using (ClassGroup.mk0_surjective (R := R))
  have hnonzero (c : ClassGroup R) : ∃ a : R, a ∈ (I c).val ∧ a ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mem_nonZeroDivisors_iff_ne_zero.mp (I c).property)
  choose a ha ha₀ using hnonzero
  let support (c : ClassGroup R) : Finset (HeightOneSpectrum R) :=
    (Ideal.finite_factors (I := Ideal.span {a c}) (by simp [ha₀ c])).toFinset
  let T : Finset (HeightOneSpectrum R) := S ∪ Finset.univ.biUnion support
  have haT : ∀ c, ∀ v ∉ (T : Set (HeightOneSpectrum R)), a c ∉ v.asIdeal := by
    intro c v hv hmem
    apply hv
    apply Finset.mem_coe.mpr
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, by
      simpa [support] using (Ideal.dvd_span_singleton.mpr hmem : v.asIdeal ∣ Ideal.span {a c})⟩
  refine ⟨T, Finset.subset_union_left, ⟨fun J => ?_⟩⟩
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  -- the contraction of `J` to `R`
  set J₀ : Ideal R := J.comap (algebraMap R ((T : Set (HeightOneSpectrum R)).integer K)) with hJ₀def
  -- every element of `J` is a `T`-unit multiple of an element of `J₀`
  have hdenom : ∀ z ∈ J, ∃ s r : R, s ≠ 0 ∧ (∀ v ∉ (T : Set (HeightOneSpectrum R)), s ∉ v.asIdeal) ∧
      r ∈ J₀ ∧ algebraMap R K s * (z : K) = algebraMap R K r := by
    intro z hz
    obtain ⟨s, hs0, hsT, r, hr⟩ := exists_mul_eq_algebraMap (K := K) T z.2
    refine ⟨s, r, hs0, hsT, ?_, hr⟩
    have h1 : algebraMap R ((T : Set (HeightOneSpectrum R)).integer K) r =
        algebraMap R ((T : Set (HeightOneSpectrum R)).integer K) s * z := Subtype.ext hr.symm
    change algebraMap R ((T : Set (HeightOneSpectrum R)).integer K) r ∈ J
    rw [h1]
    exact J.mul_mem_left _ hz
  by_cases hJ₀ : J₀ = ⊥
  · -- the zero ideal
    have hJ : J = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨s, r, hs0, -, hrJ, hr⟩ := hdenom z hz
      rw [hJ₀, Ideal.mem_bot] at hrJ
      rw [hrJ, map_zero, mul_eq_zero] at hr
      rcases hr with h | h
      · exact absurd ((map_eq_zero_iff _ hinjK).mp h) hs0
      · exact (Submodule.mem_bot _).mpr (Subtype.ext h)
    rw [hJ]
    exact bot_isPrincipal
  · -- compare `J₀` with the chosen representative of its class
    have hJ₀mem : J₀ ∈ (Ideal R)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hJ₀
    set c : ClassGroup R := ClassGroup.mk0 ⟨J₀, hJ₀mem⟩ with hc
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hI c)
    have hxy' : Ideal.span {x} * (I c).val = Ideal.span {y} * J₀ := hxy
    -- `x * a c = y * j` with `j ∈ J₀`
    have hxa : x * a c ∈ Ideal.span {y} * J₀ := by
      rw [← hxy']; exact Ideal.mem_span_singleton_mul.mpr ⟨a c, ha c, rfl⟩
    obtain ⟨j, hj, hyj⟩ := Ideal.mem_span_singleton_mul.mp hxa
    have hxK : algebraMap R K x ≠ 0 := (map_ne_zero_iff _ hinjK).mpr hx
    have hyK : algebraMap R K y ≠ 0 := (map_ne_zero_iff _ hinjK).mpr hy
    have haK : algebraMap R K (a c) ≠ 0 := (map_ne_zero_iff _ hinjK).mpr (ha₀ c)
    have hyjK : algebraMap R K y * algebraMap R K j = algebraMap R K x * algebraMap R K (a c) := by
      rw [← map_mul, ← map_mul, hyj]
    -- the generator `g = j / a c`
    let u : (T : Set (HeightOneSpectrum R)).integer K :=
      ⟨(algebraMap R K (a c))⁻¹, inv_mem_integer (K := K) _ (haT c)⟩
    let g : (T : Set (HeightOneSpectrum R)).integer K :=
      algebraMap R ((T : Set (HeightOneSpectrum R)).integer K) j * u
    have hgJ : g ∈ J := J.mul_mem_right _ hj
    refine ⟨⟨g, le_antisymm ?_ ?_⟩⟩
    · intro z hz
      obtain ⟨s, r, hs0, hsT, hrJ, hr⟩ := hdenom z hz
      have hsK : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ hinjK).mpr hs0
      -- `y * r = x * i` with `i ∈ I c`
      have hyr : y * r ∈ Ideal.span {x} * (I c).val := by
        rw [hxy']; exact Ideal.mem_span_singleton_mul.mpr ⟨r, hrJ, rfl⟩
      obtain ⟨i, -, hxi⟩ := Ideal.mem_span_singleton_mul.mp hyr
      have hxiK : algebraMap R K x * algebraMap R K i = algebraMap R K y * algebraMap R K r := by
        rw [← map_mul, ← map_mul, hxi]
      let w : (T : Set (HeightOneSpectrum R)).integer K :=
        algebraMap R ((T : Set (HeightOneSpectrum R)).integer K) i *
          ⟨(algebraMap R K s)⁻¹, inv_mem_integer (K := K) _ hsT⟩
      refine Ideal.mem_span_singleton'.mpr ⟨w, Subtype.ext ?_⟩
      change algebraMap R K i * (algebraMap R K s)⁻¹ *
        (algebraMap R K j * (algebraMap R K (a c))⁻¹) = (z : K)
      have key : algebraMap R K i * algebraMap R K j =
          algebraMap R K r * algebraMap R K (a c) := by
        apply mul_left_cancel₀ (mul_ne_zero hxK hyK)
        linear_combination (algebraMap R K y * algebraMap R K j) * hxiK +
          (algebraMap R K y * algebraMap R K r) * hyjK
      have hz' : (z : K) = algebraMap R K r * (algebraMap R K s)⁻¹ := by
        rw [← hr]; field_simp
      rw [hz']
      calc algebraMap R K i * (algebraMap R K s)⁻¹ *
            (algebraMap R K j * (algebraMap R K (a c))⁻¹)
          = (algebraMap R K i * algebraMap R K j) *
              ((algebraMap R K s)⁻¹ * (algebraMap R K (a c))⁻¹) := by ring
        _ = algebraMap R K r * (algebraMap R K s)⁻¹ := by
            rw [key]; field_simp
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hgJ

end Sol_NumberField_SClassGroup_exists_finset_isPrincipalIdealRing_integer

open Sol_NumberField_SClassGroup_exists_finset_isPrincipalIdealRing_integer in
theorem solution (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧
      IsPrincipalIdealRing ((T : Set (HeightOneSpectrum (𝓞 F))).integer F) ∧
      Subsingleton (CommRing.Pic ((T : Set (HeightOneSpectrum (𝓞 F))).integer F)) := by
  obtain ⟨T, hST, hT⟩ := exists_finset_isPrincipalIdealRing (R := 𝓞 F) (K := F) S
  exact ⟨T, hST, hT, inferInstance⟩
